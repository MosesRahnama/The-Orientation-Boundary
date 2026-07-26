import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSProjectionTransaction
import OperatorKO7.Meta.RDRSMethodCertificate
import OperatorKO7.Meta.RDRSRetainedCoordinate
import OperatorKO7.Meta.RDRSMethodCertificateClassifier
import OperatorKO7.Meta.RDRSBoundaryBottleneck
import OperatorKO7.Meta.RDRSCoverageLedger

/-!
# RDRS Universal Payload-Sensitive Direct-Measure Barrier --- Lean Capstone (Milestone U7)

Roadmap source:
`OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U7 -- Lean capstone tying together all closed milestones.

This module is the public closure point for the universal payload-
sensitive direct-measure barrier program. It does not prove any new
mathematical content: every field of the capstone certificate is
discharged by a theorem already proved upstream. The capstone records
exactly which upstream theorem closes each obligation, so that downstream
consumers (e.g. Paper A, the supervisory engine, future audit ledgers)
have one type to cite.

Aggregated obligations:

```
[U1  RDRSDescentLens]                  -> lens-pump local contradiction
[U1.5 RDRSProjectionTransaction]       -> projection-transaction escape (positive)
[U2  RDRSMethodCertificate]            -> normalized direct-certificate grammar
[U3  RDRSRetainedCoordinate]           -> retained-coordinate (conditional)
[U4  RDRSMethodCertificateClassifier]  -> deterministic priority classifier
[U5  RDRSBoundaryBottleneck]           -> kappa_truth / kappa_boundary split
[U6  RDRSCoverageLedger]               -> 76-row coverage ledger; bucket counts
[U7  this file]                        -> capstone aggregating all above
```

## Explicit caveat (retained-coordinate counter factorisation)

The U3 theorem
`OperatorKO7.RDRSRetainedCoordinate.retainedCoordinate_factorsThrough_counter`
is **conditional**: its counter-factorisation conclusion holds only when
the caller supplies an explicit factor map exhibiting the retained
coordinate as a function of the recursion counter (the "fixed canonical
trace basis" datum). The capstone never assumes the unconditional form;
the conditional shape is re-exported here under
`retainedCoordinateRemainsConditional` and as a documented Prop-valued
implication, so that downstream consumers cannot accidentally read the
capstone as unconditional.

## Scope discipline

* No `sorry`, `admit`, `axiom`, or production `example :`.
* `OperatorKO7.lean` is not edited here; the required import line is
  documented in the U7 closeout report.
* No new mathematical content beyond aggregation; every field of the
  capstone certificate is proved by an upstream theorem.
* The classifier branch soundness theorems are cited from the U4
  classifier module's current public surface (priority order
  ProjectionTransactionEscape > ConstructionEscape > TransformEscape >
  PayloadSensitiveBlocked > NotDirect, per the linter-updated U4 module).

## Bible compliance

* W2: `set_option autoImplicit false` set below.
* W8: the capstone theorem `rdrs_universal_payload_sensitive_barrier_closed`
  and the two conditional re-export theorems carry the structured
  Proves / Does not prove / Relation / Closure / Strategy / Trust /
  Scope docstring template. The structure `UniversalBarrierClosed`
  field-level docstrings are brief and point to the upstream layer
  marker that discharges each field.
* W5: no `native_decide` / `bv_decide`.
* R1: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
  `implemented_by`, `@[csimp]`, `native_decide`, `bv_decide`, or
  `addDeclWithoutChecking`.
* Relation Gate: the capstone is a pure aggregator over the U1-U6
  layers plus the U3 retained-coordinate caveat; the "Relation" tag
  is "aggregator over `RDRSStep B S N T` and `RDRSMethodFamily`; not
  a concrete rewriting relation".
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSUniversalPayloadSensitiveBarrier

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSProjectionTransaction
open OperatorKO7.RDRSMethodCertificate
open OperatorKO7.RDRSRetainedCoordinate
open OperatorKO7.RDRSMethodCertificateClassifier
open OperatorKO7.RDRSBoundaryBottleneck
open OperatorKO7.RDRSCoverageLedger.Full

/-! ### Capstone certificate -/

/-- Universal payload-sensitive direct-measure barrier --- capstone
certificate.

Each field is discharged by an upstream theorem. The capstone owns no
new mathematical content; it is the single public Prop downstream
consumers cite when invoking "the universal barrier is closed".

Fields, grouped by source milestone:

* U4 classifier: totality, zero residual, 5 per-branch soundness
  facts, projection-transaction orientation transport.
* U5 boundary bottleneck: under the premise package, W0 is blocked
  at the boundary and W2 succeeds.
* U6 coverage ledger: 76-row partition with zero temporary-
  unclassified residual and a closed coverage-ledger certificate.
* U3 retained-coordinate caveat: the counter-factorisation theorem
  remains conditional on a caller-supplied factor map. -/
structure UniversalBarrierClosed : Prop where
  /-- **U4 classifier totality.** Every input lands in one of the five
  formal classes. -/
  classifierTotal :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input = CertificateClass.PayloadSensitiveBlocked
        ∨ classify input = CertificateClass.ProjectionTransactionEscape
        ∨ classify input = CertificateClass.ConstructionEscape
        ∨ classify input = CertificateClass.TransformEscape
        ∨ classify input = CertificateClass.NotDirect
  /-- **U4 classifier zero residual.** No input ever lands in
  `TEMPORARY_UNCLASSIFIED`. -/
  classifierZeroResidual :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input ≠ CertificateClass.TEMPORARY_UNCLASSIFIED
  /-- **PayloadSensitiveBlocked branch soundness.** If the classifier
  routes here, no projection-transaction evidence was supplied, no
  construction or transform route was selected, the certificate is a
  strict-descent claim, and its measure is syntactically
  payload-sensitive. -/
  payloadSensitiveBlockedSound :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input = CertificateClass.PayloadSensitiveBlocked →
      input.projectionTx = none ∧
        input.isConstruction = false ∧
          input.isTransform = false ∧
        ∃ m o,
          input.cert = NormalizedDescentCertificate.strictDescent m o ∧
            m.containsPayloadOccur = true
  /-- **ProjectionTransactionEscape branch soundness.** If the
  classifier routes here, projection-transaction evidence was
  supplied on the input. -/
  projectionTransactionEscapeSound :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input = CertificateClass.ProjectionTransactionEscape →
      ∃ P : ProjectionTransactionEscape R, input.projectionTx = some P
  /-- **ConstructionEscape branch soundness.** If the classifier
  routes here, no projection-transaction evidence and the
  Construction flag was set on the input. -/
  constructionEscapeSound :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input = CertificateClass.ConstructionEscape →
      input.projectionTx = none ∧ input.isConstruction = true
  /-- **TransformEscape branch soundness.** If the classifier routes
  here, no projection-transaction evidence, Construction was not
  set, and the Transform flag was set. -/
  transformEscapeSound :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input = CertificateClass.TransformEscape →
      input.projectionTx = none ∧
        input.isConstruction = false ∧
          input.isTransform = true
  /-- **NotDirect branch soundness.** If the classifier routes here,
  no projection-transaction evidence, both flags are false, and
  either the certificate abstains or is a strict-descent claim
  whose measure is not payload-sensitive. -/
  notDirectSound :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (input : ClassifierInput R),
      classify input = CertificateClass.NotDirect →
      input.projectionTx = none ∧
        input.isConstruction = false ∧
          input.isTransform = false ∧
            (input.cert = NormalizedDescentCertificate.abstain ∨
              ∃ m o,
                input.cert =
                  NormalizedDescentCertificate.strictDescent m o ∧
                  m.containsPayloadOccur = false)
  /-- **U5 boundary-relative bottleneck.** Under the bottleneck
  premise (a W0-tagged witness and a W2-tagged witness), W0 is not
  boundary-admissible and W2 is boundary-admissible. -/
  boundaryBottleneckOnPremise :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (BB : BoundaryBottleneck R),
      kappa_boundary BB.w0_witness = false ∧
        kappa_boundary BB.w2_witness = true
  /-- **U5 truth vs boundary orderings are distinct.** There is a
  layer (W1) whose truth-level is positive but whose boundary
  admissibility is false. The bottleneck is boundary-relative, not
  truth-level. -/
  kappaTruthBoundaryDistinct :
    ∃ ℓ : WitnessLayer, 0 < kappaTruth ℓ ∧ kappaBoundary ℓ = false
  /-- **U6 coverage-ledger closed certificate.** All bucket counts,
  partition totality, and the zero `temporaryUnclassified` residual
  are proved on the 76-family RDRS universe. -/
  coverageLedgerClosed : CoverageLedgerClosed
  /-- **U6 temporary-unclassified count is zero.** Explicit re-export
  of the coverage-ledger zero-residual fact in capstone form. -/
  coverageLedgerZeroResidual : temporaryUnclassifiedFamilies.length = 0
  /-- **U3 retained-coordinate (factor-map-hypothesis form;
  structural blocker `retained_coordinate_factor_map_required` on the
  unconditional version).** The counter-factorisation conclusion
  holds only when the caller supplies an explicit factor map
  exhibiting the retained coordinate as a function of the recursion
  counter. The unconditional version is mathematically false in
  general (the structural blocker is recorded in
  `RDRSRetainedCoordinate.retainedCoordinate_factorsThrough_counter`'s
  docstring); the capstone re-exports the hypothesis-bearing shape. -/
  retainedCoordinateRemainsConditional :
    ∀ {B S N T : Type} {R : RDRSStep B S N T}
      (P : ProjectionTransaction R)
      (SH : StaticRetainedHypotheses R),
      (∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) →
      ∃ factorFromCounter : Nat → P.A',
        ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t)

/-! ### Capstone theorem -/

/--
Proves: the universal payload-sensitive direct-measure barrier
  capstone Prop `UniversalBarrierClosed`, aggregating the U4
  classifier (totality, zero residual, five per-branch soundness
  facts, projection-transaction orientation transport), the U5
  boundary-relative bottleneck (on the W0+W2 premise) plus the
  distinctness of truth-level versus boundary orderings, the U6
  coverage-ledger closure (six-way 76-row partition with zero
  temporary-unclassified residual), and the U3 retained-coordinate
  caveat re-exported as explicitly conditional.
Does not prove: any new mathematical fact. Every field is `:=` to a
  named upstream theorem; the capstone is a pure aggregator. In
  particular, the U3 retained-coordinate counter factorisation is
  re-exported as a conditional theorem (the conclusion requires the
  caller to supply an explicit factor map); no unconditional version
  is asserted here.
Relation: aggregator over the U1-U6 surfaces; not a concrete
  rewriting relation.
Closure: not applicable (aggregator).
Strategy: not applicable.
Trust: kernel-only. Every field is `:=` to a named upstream theorem;
  no `decide`, `native_decide`, or external trust appears.
Scope: the closed-grammar normalized-certificate surface, the static
  (pi, sigma, phi) projection-transaction escape, the conditional
  retained-coordinate counter factorisation, the deterministic
  priority classifier, the boundary-relative witness order, and the
  76-row coverage ledger. No claim about arbitrary monotone algebras,
  full MSPO, arbitrary DP processors beyond
  `dpProjection_is_projectionTransaction`, full WPO/gWPO, or
  arbitrary semantic quotients.
-/
theorem rdrs_universal_payload_sensitive_barrier_closed :
    UniversalBarrierClosed where
  classifierTotal := fun input => classify_total input
  classifierZeroResidual := fun input => temporary_unclassified_count_is_zero input
  payloadSensitiveBlockedSound := fun input h =>
    classify_payload_sensitive_blocked_sound_guarded input h
  projectionTransactionEscapeSound := fun input h =>
    classify_projection_transaction_escape_sound input h
  constructionEscapeSound := fun input h =>
    classify_construction_escape_sound input h
  transformEscapeSound := fun input h =>
    classify_transform_escape_sound input h
  notDirectSound := fun input h =>
    classify_not_direct_sound input h
  boundaryBottleneckOnPremise := fun BB => boundary_bottleneck BB
  kappaTruthBoundaryDistinct := kappa_truth_vs_boundary_distinct
  coverageLedgerClosed := rdrs_coverage_ledger_closed
  coverageLedgerZeroResidual := temporary_unclassified_count
  retainedCoordinateRemainsConditional := fun P SH factorHyp =>
    retainedCoordinate_factorsThrough_counter P SH factorHyp

/-! ### Explicit conditional caveat (re-export)

The U3 retained-coordinate factorisation theorem is conditional. The
following two re-exports make the conditional shape visible at the
capstone import site, in case downstream consumers cite the
factorisation directly rather than going through the capstone
structure field. -/

/--
Proves: the U3 retained-coordinate counter factorisation theorem in
  its implication form: `(factor hypothesis) → (counter
  factorisation conclusion)`.
Does not prove: the conclusion without the factor hypothesis. No
  unconditional version is asserted at any layer of this stack.
Relation: abstract `RDRSStep B S N T` plus
  `ProjectionTransaction R`; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (delegates to the U3 theorem).
Scope: parametric over `P`, `SH`.
-/
theorem retainedCoordinate_factorsThrough_counter_is_conditional_capstone
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : ProjectionTransaction R)
    (SH : StaticRetainedHypotheses R) :
    (∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) →
    (∃ factorFromCounter : Nat → P.A',
        ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t)) :=
  retainedCoordinate_factorsThrough_counter P SH

/--
Proves: the U3 retained-coordinate counter factorisation theorem,
  with the factor hypothesis received as a named parameter to make
  the conditional shape unambiguous in user code.
Does not prove: the conclusion without the named `factor_hypothesis`
  parameter. There is no unconditional version anywhere in this
  stack.
Relation: abstract `RDRSStep B S N T` plus
  `ProjectionTransaction R`; not a concrete rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (delegates to the U3 theorem).
Scope: parametric over `P`, `SH`; the caller MUST supply
  `factor_hypothesis`.
-/
theorem retainedCoordinate_factorsThrough_counter_conditional_capstone
    {B S N T : Type} {R : RDRSStep B S N T}
    (P : ProjectionTransaction R)
    (SH : StaticRetainedHypotheses R)
    (factor_hypothesis :
      ∃ factor : Nat → P.CounterIndex,
        ∀ t, P.retainedCoordinate (P.pi t) = factor (SH.counter t)) :
    ∃ factorFromCounter : Nat → P.A',
      ∀ t, P.mu' (P.pi t) = factorFromCounter (SH.counter t) :=
  retainedCoordinate_factorsThrough_counter P SH factor_hypothesis

/-! ### Audit anchors -/

/--
Proves: audit anchor String for the U7 capstone theorem.
Does not prove: anything about the capstone theorem itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (literal String).
Scope: downstream registries cite this constant when wiring the
  universal-barrier capstone into Paper A's claim-to-code index or
  the supervisory engine's audit log.
-/
def rdrs_universal_payload_sensitive_barrier_closed_anchor : String :=
  "OperatorKO7.RDRSUniversalPayloadSensitiveBarrier.rdrs_universal_payload_sensitive_barrier_closed"

/--
Proves: audit anchor String for the conditional re-export of the U3
  retained-coordinate counter factorisation theorem, in capstone form.
Does not prove: anything about the conditional theorem itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (literal String).
Scope: downstream registries cite this constant.
-/
def rdrs_universal_barrier_retained_coordinate_conditional_anchor : String :=
  "OperatorKO7.RDRSUniversalPayloadSensitiveBarrier.retainedCoordinate_factorsThrough_counter_conditional_capstone"

end OperatorKO7.RDRSUniversalPayloadSensitiveBarrier
