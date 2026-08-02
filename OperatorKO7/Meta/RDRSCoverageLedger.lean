import OperatorKO7.Meta.RDRSCoverageLedgerSeed
import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSeedCollapse
import OperatorKO7.Meta.RDRSProjectionTransaction
import OperatorKO7.Meta.RDRSRetainedCoordinate
import OperatorKO7.Meta.RDRSWitnessTransport
import OperatorKO7.Meta.RDRSMethodCertificate

set_option autoImplicit false

/-!
# RDRS Coverage Ledger (Milestone U6)

Roadmap source: `OperatorKO7/Expansion/Universal_Payload_Sensitive_Direct_Measures_Roadmap.md`
Milestone U6 -- Generated Coverage Ledger.

This module is the referee-facing audit ledger for the universal payload-
sensitive direct-measure barrier program. Every row of the 76-family RDRS
termination-method universe (closed at
`OperatorKO7.RDRSTerminationMethodUniverseCloseout`) is given a ten-column
audit record:

```
| family
| raw constructor / method family
| normalized certificate status
| lens theorem
| seed-collapse status
| projection transaction status
| retained coordinate status
| classification (6-way)
| Lean theorem identifier
| Paper A claim supported
```

## Classifier discipline

The six-way classifier (`U6Classification`) refines the five-way U3 seed
classifier with the roadmap's mandatory `transformEscape` bucket separating
licensed-transformation escapes (DP-style, integer-TRS, CPS) from raw path-
order / typing constructions. A sixth bucket `temporaryUnclassified`
records the residual obligation that the roadmap requires to be empty for
the final direct-measure universe.

```
[normalized direct method certificate]
    |
    +--> payloadSensitiveBlocked    (direct + payload-sensitive + lens-pump)
    +--> projectionTransactionEscape (static (pi, sigma, phi) + retained counter)
    +--> constructionEscape          (path-order / typing construction)
    +--> transformEscape             (DP / size-change / CPS / TRS-extension)
    +--> notDirect                   (violates direct syntax / interface)
    +--> temporaryUnclassified       (residual; final count = 0)
```

## Final closeout theorems

```
rdrs_coverage_ledger_closed : CoverageLedgerClosed
  + temporary_unclassified_count : temporaryUnclassifiedFamilies.length = 0
  + u6_partition_total           : sum of bucket counts = 76
  + rdrsFullCoverageLedger_length: 76
  + u6ClassOf_total              : six-way classification is total
```

## Scope discipline

* No `sorry`, `admit`, `axiom`, or production `example :`.
* `OperatorKO7.lean` is not edited here; the required import line is
  documented in the U6 closeout report.
* Per-family identifiers in `leanTheoremIdentifierOf` reuse the existing
  `OperatorKO7.RDRSCoverageLedger.theoremIdOf` map from the U3 seed; the
  ledger does not invent new Lean names.
* The classifier extends the U3 seed without revising its existing five-
  way classes; the only refinement is splitting U3's `constructionEscape`
  into `constructionEscape` (path-order / typing) versus `transformEscape`
  (DP / transformed-method / CPS / TRS-extension), and moving conditional
  rows from `needsDirectUniverseProof` to their appropriate U6 bucket.
-/

namespace OperatorKO7.RDRSCoverageLedger.Full

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSCoverageLedger

/-! ## Six-way U6 classification -/

/-- Six-way classifier required by the universal payload-sensitive direct-
measures roadmap, Milestone U6. -/
inductive U6Classification
  /-- Direct certificate, payload-sensitive measure, blocked by the
  B-parametric lens-pump barrier. Includes conditional rows whose
  hypothesis discharges to direct payload-sensitive descent. -/
  | payloadSensitiveBlocked
  /-- Successful escape via a static RDRS projection transaction
  `(pi, sigma, phi)` with seed-collapse forgetting and retained-coordinate
  factorisation through the recursion counter. -/
  | projectionTransactionEscape
  /-- Outside the direct payload-sensitive grammar because of a non-direct
  construction (path-order, AC RPO, Cichon slow-growing, typing-based
  barriers). -/
  | constructionEscape
  /-- Outside the direct payload-sensitive grammar because the method
  routes through a licensed transformation (DP / size-change / CPS /
  TRS-extension / sharing-aware quasi-interpretation). -/
  | transformEscape
  /-- Violates the direct payload-sensitive direct-measure syntax or
  interface (semantic labeling, neutral DP processors, abstract
  interpretation, etc.). -/
  | notDirect
  /-- Residual classification slot. The roadmap requires this bucket's
  count to be zero for the final direct-measure universe. -/
  | temporaryUnclassified
  deriving DecidableEq, Repr

/-! ## Ledger row structure (10 columns) -/

/-- Ten-column audit record for one RDRS termination-method family.

| Column | Field name | Content |
|---|---|---|
| family | `family` | the closed enum row |
| raw constructor | `rawConstructor` | high-level constructor / method-family string |
| normalized certificate | `normalizedCertificate` | normalized-certificate status string |
| lens theorem | `lensTheorem` | lens-pump theorem identifier for the row's class |
| seed-collapse status | `seedCollapseStatus` | seed-collapse / payload-forgetting status |
| projection transaction status | `projectionTransactionStatus` | (pi, sigma, phi) status |
| retained coordinate status | `retainedCoordinateStatus` | retained-coordinate factorisation status |
| classification | `classification` | six-way `U6Classification` value |
| Lean theorem identifier | `leanTheoremIdentifier` | existing Lean theorem identifier for this row |
| Paper A claim supported | `paperAClaimSupported` | Paper A claim / section reference |

All String fields are metadata; only the `family` and `classification`
fields are type-checked beyond String equality. -/
structure RDRSCoverageLedgerRow where
  family                      : RDRSMethodFamily
  rawConstructor              : String
  normalizedCertificate       : String
  lensTheorem                 : String
  seedCollapseStatus          : String
  projectionTransactionStatus : String
  retainedCoordinateStatus    : String
  classification              : U6Classification
  leanTheoremIdentifier       : String
  paperAClaimSupported        : String
  deriving DecidableEq, Repr

/-! ## Six-way classification of all 76 families -/

/-- Six-way U6 classification for every row in the 76-family RDRS
universe. -/
def u6ClassOf : RDRSMethodFamily → U6Classification
  -- KBO payload-sensitive blocked (6)
  | .standardKBO                      => .payloadSensitiveBlocked
  | .kboWithStatus                    => .payloadSensitiveBlocked
  | .generalizedKBO                   => .payloadSensitiveBlocked
  | .acKBO                            => .payloadSensitiveBlocked
  | .transfiniteKBO                   => .payloadSensitiveBlocked
  | .lambdaFreeKBO                    => .payloadSensitiveBlocked
  -- DP projection-transaction escape (7)
  | .subtermCoefficientKBO            => .projectionTransactionEscape
  -- Path-order construction escape (5)
  | .acRPO                            => .constructionEscape
  | .rpoModuloPermutation             => .constructionEscape
  | .popStarFamily                    => .constructionEscape
  | .simpleTerminationOrderType       => .constructionEscape
  | .cichonSlowGrowing                => .constructionEscape
  -- Polynomial / max / matrix payload-sensitive blocked (10)
  | .linearPolyQ                      => .payloadSensitiveBlocked
  | .linearPolyR                      => .payloadSensitiveBlocked
  | .negativeCoefficientPolynomial    => .payloadSensitiveBlocked
  | .maxPolynomial                    => .payloadSensitiveBlocked
  | .nonlinearHigherDegreePolynomial  => .payloadSensitiveBlocked
  | .multilinearInterpretation        => .payloadSensitiveBlocked
  | .matrixNScalarProjection          => .payloadSensitiveBlocked
  | .matrixQRScalarProjection         => .payloadSensitiveBlocked
  | .arcticScalarProjection           => .payloadSensitiveBlocked
  | .tropicalScalarProjection         => .payloadSensitiveBlocked
  | .triangularMatrix                 => .payloadSensitiveBlocked
  -- Tuple / higher-order / poly-KBO conditional blocked (3)
  | .tupleInterpretationStrictS       => .payloadSensitiveBlocked
  | .higherOrderTupleInterpretation   => .payloadSensitiveBlocked
  | .polynomialKBO                    => .payloadSensitiveBlocked
  -- Semantic / structural payload-sensitive blocked (4)
  | .strictMonotoneAlgebraArchimedean => .payloadSensitiveBlocked
  | .extendedMonotoneAlgebra          => .payloadSensitiveBlocked
  | .finiteModelTermination           => .payloadSensitiveBlocked
  | .matchBounds                      => .payloadSensitiveBlocked
  | .raiseConsistencyMatchBounds      => .payloadSensitiveBlocked
  -- Semantic labeling family: not direct (4)
  | .semanticLabeling                 => .notDirect
  | .predictiveLabeling               => .notDirect
  | .rootLabeling                     => .notDirect
  | .selfLabelingEquational           => .notDirect
  -- Categorical / topos / forward-closures / quasi-decreasingness: notDirect (3)
  | .categoricalToposTermination      => .notDirect
  | .forwardClosures                  => .notDirect
  | .quasiDecreasingness              => .notDirect
  -- DP processors: projection-transaction escapes (7)
  | .dpProcessorClassification        => .projectionTransactionEscape
  | .dpSubtermCriterion               => .projectionTransactionEscape
  | .dpArgumentFiltering              => .projectionTransactionEscape
  | .dpReductionPairProcessor         => .projectionTransactionEscape
  | .orderSortedDP                    => .projectionTransactionEscape
  | .contextSensitiveDP               => .projectionTransactionEscape
  | .twoDDPForCTRS                    => .projectionTransactionEscape
  -- DP-neutral / formative-rules: notDirect (3)
  | .dpNeutralProcessors              => .notDirect
  | .dpReductionTriples               => .notDirect
  | .formativeRules                   => .notDirect
  -- Usable-rules: transform escape (DP side condition)
  | .usableRulesMinimality            => .transformEscape
  -- Type-introduction / many-sorted persistence: transform escape (2)
  | .typeIntroduction                 => .transformEscape
  | .manySortedPersistence            => .transformEscape
  -- CTRS operational termination: notDirect
  | .operationalTerminationCTRS       => .notDirect
  -- Integer / LCTRS / HO LCTRS: transform escape (3)
  | .integerTermRewriting             => .transformEscape
  | .lctrs                            => .transformEscape
  | .higherOrderLCTRS                 => .transformEscape
  -- HORPO / CPO / general-schema / sized-types / Coq guard: notDirect (5)
  | .horpoAdmittance                  => .notDirect
  | .cpoAdmittance                    => .notDirect
  | .generalSchemaAdmittance          => .notDirect
  | .sizedTypesAdmittance             => .notDirect
  | .coqGuardAdmittance               => .notDirect
  -- Typing barriers: construction escape (3)
  | .bellantoniCookSplit              => .constructionEscape
  | .linearLogicTypingBarrier         => .constructionEscape
  | .ramifiedRecursionTypingBarrier   => .constructionEscape
  -- Sharing / type-graph / equational quotient: transform escape (4)
  | .sharingNonConservativity         => .transformEscape
  | .weightedTypeGraphEscape          => .transformEscape
  | .generalizedWeightedTypeGraphs    => .transformEscape
  | .equationalQuotientNonConservativity => .transformEscape
  -- Cycle / string / infinitary / abstract: notDirect (4)
  | .cycleRewritingInapplicability    => .notDirect
  | .stringRewritingInapplicability   => .notDirect
  | .infinitaryRewritingTermination   => .notDirect
  | .abstractInterpretationAdmittance => .notDirect
  -- Left-linear match bounds: payload-sensitive blocked (conditional)
  | .leftLinearMatchBounds            => .payloadSensitiveBlocked
  -- Size-change termination: projection-transaction escape
  | .sizeChangeTerminationEscape      => .projectionTransactionEscape
  -- Pi-calculus / lambda-mu CPS / quasi-interpretations: transform escape (3)
  | .piCalculusTerminationTranslation => .transformEscape
  | .lambdaMuSNViaCPS                 => .transformEscape
  | .quasiInterpretationsSharingAware => .transformEscape

/-! ## Per-class metadata helpers -/

/-- Lens theorem identifier for the row's classification. The blocked and
projection-transaction-escape classes both cite the local-contradiction
theorem, but with opposite polarity (blocked = lens violation; projection
= positive projected orientation). -/
def lensTheoremOfClass : U6Classification → String
  | .payloadSensitiveBlocked
      => "OperatorKO7.RDRSDescentLens.no_orients_of_lens_violation"
  | .projectionTransactionEscape
      => "OperatorKO7.RDRSProjectionTransaction.ProjectionTransactionEscape.lifted_orients"
  | .constructionEscape
      => "n/a: outside direct lens-pump grammar"
  | .transformEscape
      => "n/a: lens applies on the transformed system, not the source RDRS"
  | .notDirect
      => "n/a: violates direct certificate syntax"
  | .temporaryUnclassified
      => "n/a"

/-- Seed-collapse status for the row's classification. -/
def seedCollapseStatusOfClass : U6Classification → String
  | .payloadSensitiveBlocked
      => "carrier-insensitive observable factors through SeedCollapse; payload diagonal preserved across step"
  | .projectionTransactionEscape
      => "SeedCollapse + FactorsThroughSeedCollapse witness on pi; phi obligation discharged"
  | .constructionEscape
      => "n/a: construction outside seed-collapse grammar"
  | .transformEscape
      => "transformed system has its own carrier; seed-collapse does not apply to source rules"
  | .notDirect
      => "n/a"
  | .temporaryUnclassified
      => "n/a"

/-- Paper A claim that the row supports. -/
def paperAClaimOfClass : U6Classification → String
  | .payloadSensitiveBlocked
      => "Universal direct payload-sensitive barrier (Paper A: Projection transactions and the canonical retained coordinate)"
  | .projectionTransactionEscape
      => "DP projection as projection transaction; retained coordinate factors through the counter (Paper A: Projection transactions)"
  | .constructionEscape
      => "Construction outside direct payload-sensitive grammar (Paper A: Boundary dichotomy)"
  | .transformEscape
      => "Licensed-transformation escape outside direct grammar (Paper A: Boundary dichotomy)"
  | .notDirect
      => "Violates direct payload-sensitive syntax/interface (Paper A: Normalized certificate grammar)"
  | .temporaryUnclassified
      => "n/a"

/-! ## Per-family metadata: raw constructor / certificate / transaction -/

/-- Raw constructor or method family. High-level method-family description
of the row. -/
def rawConstructorOf : RDRSMethodFamily → String
  | .standardKBO | .kboWithStatus | .generalizedKBO
      => "KBO with payload-mentioning weight (standard / status / generalized)"
  | .acKBO | .transfiniteKBO | .lambdaFreeKBO
      => "KBO variant (AC / transfinite / lambda-free)"
  | .subtermCoefficientKBO
      => "Subterm-coefficient KBO (argument-filtered subterm projection)"
  | .acRPO | .rpoModuloPermutation | .popStarFamily
      => "Path-order construction (AC RPO / permutation-modular RPO / POP*)"
  | .simpleTerminationOrderType
      => "Simple-termination order-type construction (conditional)"
  | .cichonSlowGrowing
      => "Cichon slow-growing path-order construction"
  | .linearPolyQ | .linearPolyR
      => "Linear polynomial interpretation over Q or R"
  | .negativeCoefficientPolynomial
      => "Polynomial with negative coefficients (conditional EventuallyDominatedAtBase)"
  | .maxPolynomial
      => "Max-polynomial interpretation"
  | .nonlinearHigherDegreePolynomial
      => "Nonlinear higher-degree polynomial (conditional pump hypothesis)"
  | .multilinearInterpretation
      => "Multilinear polynomial interpretation"
  | .matrixNScalarProjection | .matrixQRScalarProjection
      => "Matrix interpretation with scalar projection (N or QR)"
  | .arcticScalarProjection
      => "Arctic matrix scalar projection (max-plus algebra)"
  | .tropicalScalarProjection
      => "Tropical matrix scalar projection (min-plus algebra)"
  | .triangularMatrix
      => "Triangular matrix interpretation"
  | .tupleInterpretationStrictS
      => "Tuple interpretation, strict on s coordinate (conditional)"
  | .higherOrderTupleInterpretation
      => "Higher-order tuple interpretation (conditional)"
  | .polynomialKBO
      => "Polynomial KBO weight (conditional payload-sensitive weight)"
  | .strictMonotoneAlgebraArchimedean
      => "Strict monotone Archimedean algebra"
  | .extendedMonotoneAlgebra
      => "Extended monotone algebra (conditional Archimedean extension)"
  | .semanticLabeling | .predictiveLabeling | .rootLabeling | .selfLabelingEquational
      => "Semantic labeling family (semantic / predictive / root / self-labeling)"
  | .finiteModelTermination
      => "Finite-model decreasing weight"
  | .categoricalToposTermination
      => "Categorical / topos-theoretic termination interpretation"
  | .forwardClosures
      => "Forward-closures admittance"
  | .matchBounds
      => "Match-bounds counter measure"
  | .raiseConsistencyMatchBounds
      => "Raise-consistency match-bounds"
  | .quasiDecreasingness
      => "Quasi-decreasingness for CTRS"
  | .dpProcessorClassification | .dpSubtermCriterion | .dpArgumentFiltering
  | .dpReductionPairProcessor
      => "Dependency pair processor (subterm / argument-filtering / reduction-pair)"
  | .dpNeutralProcessors | .dpReductionTriples
      => "Neutral / non-orienting DP processor"
  | .usableRulesMinimality
      => "Usable-rules minimality side-condition on DP problem"
  | .formativeRules
      => "Formative rules side-marker"
  | .typeIntroduction
      => "Type-introduction transform on TRS"
  | .manySortedPersistence
      => "Many-sorted persistence transform"
  | .orderSortedDP | .contextSensitiveDP
      => "Order-sorted / context-sensitive DP processor"
  | .twoDDPForCTRS
      => "2D dependency pairs for CTRS"
  | .operationalTerminationCTRS
      => "Operational-termination CTRS criterion"
  | .integerTermRewriting
      => "Integer-domain term rewriting"
  | .lctrs | .higherOrderLCTRS
      => "LCTRS / higher-order LCTRS"
  | .horpoAdmittance | .cpoAdmittance | .generalSchemaAdmittance
      => "Higher-order admittance criterion (HORPO / CPO / general schema)"
  | .sizedTypesAdmittance | .coqGuardAdmittance
      => "Type-system admittance (sized types / Coq guard condition)"
  | .bellantoniCookSplit
      => "Bellantoni-Cook safe/normal argument split"
  | .linearLogicTypingBarrier
      => "Linear-logic typing barrier"
  | .ramifiedRecursionTypingBarrier
      => "Ramified-recursion typing barrier"
  | .sharingNonConservativity
      => "Sharing non-conservative transform"
  | .weightedTypeGraphEscape
      => "Weighted-type-graph escape transform"
  | .generalizedWeightedTypeGraphs
      => "Generalized weighted-type-graph transform"
  | .equationalQuotientNonConservativity
      => "Equational-quotient non-conservative transform"
  | .cycleRewritingInapplicability
      => "Cycle-rewriting inapplicability marker"
  | .stringRewritingInapplicability
      => "String-rewriting inapplicability marker"
  | .leftLinearMatchBounds
      => "Left-linear match-bounds (conditional left-linearity)"
  | .sizeChangeTerminationEscape
      => "Size-change termination (change-matrix projection)"
  | .infinitaryRewritingTermination
      => "Infinitary-rewriting termination"
  | .piCalculusTerminationTranslation
      => "Pi-calculus termination translation"
  | .lambdaMuSNViaCPS
      => "Lambda-mu SN via CPS translation"
  | .abstractInterpretationAdmittance
      => "Abstract-interpretation admittance"
  | .quasiInterpretationsSharingAware
      => "Sharing-aware quasi-interpretation transform"

/-- Normalized certificate status string. -/
def normalizedCertificateOf : RDRSMethodFamily → String
  | .standardKBO | .kboWithStatus | .generalizedKBO | .acKBO | .transfiniteKBO | .lambdaFreeKBO
      => "strictDescent (KBO weight with payload counter, payload coefficient at least 1)"
  | .subtermCoefficientKBO
      => "strictDescent (post-filter KBO weight on retained subterm)"
  | .acRPO | .rpoModuloPermutation | .popStarFamily | .simpleTerminationOrderType
  | .cichonSlowGrowing
      => "abstain (path-order construction outside direct certificate grammar)"
  | .linearPolyQ | .linearPolyR | .maxPolynomial | .multilinearInterpretation
  | .matrixNScalarProjection | .matrixQRScalarProjection | .arcticScalarProjection
  | .tropicalScalarProjection | .triangularMatrix
      => "strictDescent (algebraic interpretation with payload-mentioning coefficient)"
  | .negativeCoefficientPolynomial | .nonlinearHigherDegreePolynomial
  | .tupleInterpretationStrictS | .higherOrderTupleInterpretation | .polynomialKBO
  | .extendedMonotoneAlgebra | .leftLinearMatchBounds
      => "strictDescent (conditional payload-sensitive certificate; hypothesis required)"
  | .strictMonotoneAlgebraArchimedean | .finiteModelTermination
  | .matchBounds | .raiseConsistencyMatchBounds
      => "strictDescent (semantic / structural payload-sensitive certificate)"
  | .semanticLabeling | .predictiveLabeling | .rootLabeling | .selfLabelingEquational
  | .quasiDecreasingness | .categoricalToposTermination | .forwardClosures
      => "abstain (semantic relabeling / quotient outside direct certificate grammar)"
  | .dpProcessorClassification | .dpSubtermCriterion | .dpArgumentFiltering
  | .dpReductionPairProcessor | .orderSortedDP | .contextSensitiveDP | .twoDDPForCTRS
      => "strictDescent (post-projection certificate on DP problem's retained coordinate)"
  | .sizeChangeTerminationEscape
      => "strictDescent (size-change projection certificate; pi factors through change-matrix)"
  | .dpNeutralProcessors | .dpReductionTriples | .formativeRules
      => "abstain (no orientation produced; side-marker only)"
  | .usableRulesMinimality
      => "strictDescent (post-transform DP certificate under usable-rules side condition)"
  | .typeIntroduction | .manySortedPersistence
      => "strictDescent (post-transform certificate on typed system)"
  | .operationalTerminationCTRS | .horpoAdmittance | .cpoAdmittance
  | .generalSchemaAdmittance | .sizedTypesAdmittance | .coqGuardAdmittance
      => "abstain (admittance / interface criterion outside direct certificate grammar)"
  | .integerTermRewriting | .lctrs | .higherOrderLCTRS
      => "strictDescent (post-transform certificate on extended TRS)"
  | .bellantoniCookSplit | .linearLogicTypingBarrier | .ramifiedRecursionTypingBarrier
      => "abstain (typing barrier; outside direct certificate grammar)"
  | .sharingNonConservativity | .weightedTypeGraphEscape | .generalizedWeightedTypeGraphs
  | .equationalQuotientNonConservativity | .piCalculusTerminationTranslation
  | .lambdaMuSNViaCPS | .quasiInterpretationsSharingAware
      => "strictDescent (post-transform certificate on transformed system)"
  | .cycleRewritingInapplicability | .stringRewritingInapplicability
  | .infinitaryRewritingTermination | .abstractInterpretationAdmittance
      => "abstain (inapplicability / out-of-scope marker)"

/-- Projection transaction status per family. -/
def projectionTransactionStatusOf : RDRSMethodFamily → String
  | .dpProcessorClassification | .dpSubtermCriterion | .dpArgumentFiltering
  | .dpReductionPairProcessor | .orderSortedDP | .contextSensitiveDP | .twoDDPForCTRS
      => "DPProjectionEscape: dpProjection_is_projectionTransaction; pi factors through DP problem"
  | .subtermCoefficientKBO
      => "Argument-filtered subterm projection: pi factors through filtered subterm"
  | .sizeChangeTerminationEscape
      => "Size-change projection: pi factors through accumulated change-matrix"
  | .standardKBO | .kboWithStatus | .generalizedKBO | .acKBO | .transfiniteKBO
  | .lambdaFreeKBO | .linearPolyQ | .linearPolyR | .negativeCoefficientPolynomial
  | .maxPolynomial | .nonlinearHigherDegreePolynomial | .multilinearInterpretation
  | .matrixNScalarProjection | .matrixQRScalarProjection | .arcticScalarProjection
  | .tropicalScalarProjection | .triangularMatrix | .tupleInterpretationStrictS
  | .higherOrderTupleInterpretation | .polynomialKBO | .strictMonotoneAlgebraArchimedean
  | .extendedMonotoneAlgebra | .finiteModelTermination | .matchBounds
  | .raiseConsistencyMatchBounds | .leftLinearMatchBounds
      => "no projection transaction needed: direct barrier fires"
  | .acRPO | .rpoModuloPermutation | .popStarFamily | .simpleTerminationOrderType
  | .cichonSlowGrowing | .bellantoniCookSplit | .linearLogicTypingBarrier
  | .ramifiedRecursionTypingBarrier
      => "n/a: construction outside (pi, sigma, phi) grammar"
  | .typeIntroduction | .manySortedPersistence | .integerTermRewriting | .lctrs
  | .higherOrderLCTRS | .usableRulesMinimality | .sharingNonConservativity
  | .weightedTypeGraphEscape | .generalizedWeightedTypeGraphs
  | .equationalQuotientNonConservativity | .piCalculusTerminationTranslation
  | .lambdaMuSNViaCPS | .quasiInterpretationsSharingAware
      => "transformed system has its own projection apparatus; not a source-side static transaction"
  | .semanticLabeling | .predictiveLabeling | .rootLabeling | .selfLabelingEquational
  | .quasiDecreasingness | .categoricalToposTermination | .forwardClosures
  | .dpNeutralProcessors | .dpReductionTriples | .formativeRules
  | .operationalTerminationCTRS | .horpoAdmittance | .cpoAdmittance
  | .generalSchemaAdmittance | .sizedTypesAdmittance | .coqGuardAdmittance
  | .cycleRewritingInapplicability | .stringRewritingInapplicability
  | .infinitaryRewritingTermination | .abstractInterpretationAdmittance
      => "n/a: outside direct payload-sensitive interface"

/-- Retained-coordinate status per family. -/
def retainedCoordinateStatusOf : RDRSMethodFamily → String
  | .dpProcessorClassification | .dpSubtermCriterion | .dpArgumentFiltering
  | .dpReductionPairProcessor | .orderSortedDP | .contextSensitiveDP | .twoDDPForCTRS
      => "retainedCoordinate_factorsThrough_counter via DP problem's projected counter"
  | .subtermCoefficientKBO
      => "retainedCoordinate is the filtered-subterm position; factors through counter under static hypothesis"
  | .sizeChangeTerminationEscape
      => "retainedCoordinate is the change-matrix index; factors through counter via accumulated decreases"
  | .standardKBO | .kboWithStatus | .generalizedKBO | .acKBO | .transfiniteKBO
  | .lambdaFreeKBO | .linearPolyQ | .linearPolyR | .negativeCoefficientPolynomial
  | .maxPolynomial | .nonlinearHigherDegreePolynomial | .multilinearInterpretation
  | .matrixNScalarProjection | .matrixQRScalarProjection | .arcticScalarProjection
  | .tropicalScalarProjection | .triangularMatrix | .tupleInterpretationStrictS
  | .higherOrderTupleInterpretation | .polynomialKBO | .strictMonotoneAlgebraArchimedean
  | .extendedMonotoneAlgebra | .finiteModelTermination | .matchBounds
  | .raiseConsistencyMatchBounds | .leftLinearMatchBounds
      => "n/a: no projection branch; direct measure on payload counter"
  | .acRPO | .rpoModuloPermutation | .popStarFamily | .simpleTerminationOrderType
  | .cichonSlowGrowing | .bellantoniCookSplit | .linearLogicTypingBarrier
  | .ramifiedRecursionTypingBarrier
      => "n/a: construction outside retained-counter grammar"
  | .typeIntroduction | .manySortedPersistence | .integerTermRewriting | .lctrs
  | .higherOrderLCTRS | .usableRulesMinimality | .sharingNonConservativity
  | .weightedTypeGraphEscape | .generalizedWeightedTypeGraphs
  | .equationalQuotientNonConservativity | .piCalculusTerminationTranslation
  | .lambdaMuSNViaCPS | .quasiInterpretationsSharingAware
      => "n/a: retained coordinate lives on the transformed system"
  | .semanticLabeling | .predictiveLabeling | .rootLabeling | .selfLabelingEquational
  | .quasiDecreasingness | .categoricalToposTermination | .forwardClosures
  | .dpNeutralProcessors | .dpReductionTriples | .formativeRules
  | .operationalTerminationCTRS | .horpoAdmittance | .cpoAdmittance
  | .generalSchemaAdmittance | .sizedTypesAdmittance | .coqGuardAdmittance
  | .cycleRewritingInapplicability | .stringRewritingInapplicability
  | .infinitaryRewritingTermination | .abstractInterpretationAdmittance
      => "n/a"

/-- Lean theorem identifier per family. Delegates to the U3 seed's
`theoremIdOf` for the existing-theorem map, with explicit overrides for
the three U3-seed rows whose String cites a theorem that does not
actually exist in the `OperatorKO7` Lean tree:

* KBO standard family (standardKBO / kboWithStatus / generalizedKBO):
  U3 cited `SymbolicComparatorBarrier.no_global_step_orientation_symbolic_comparator`
  which is not a Lean theorem; the existing barrier theorem is
  `KBO_Impossible.no_kbo_orients_ko7_rec_succ_trace`.
* KBO variants (acKBO / transfiniteKBO / lambdaFreeKBO):
  U3 cited `BarrierClass_Classifier.ko7BarrierClassifier.complete`
  which is not a Lean theorem; the existing path-order layer marker is
  `RDRSPathOrderDichotomy.kboBarrierVariant_no_symbolic_orientation`.
* Matrix arbitrary families (matrixNScalarProjection /
  matrixQRScalarProjection / triangularMatrix):
  U3 cited `MatrixBarrierArbitrary.matrix_barrier_arbitrary_all_blocked`
  which is not a Lean theorem; the existing barrier theorem is
  `MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump`.

The ledger does not invent new Lean names; every override below names a
theorem that already exists in the OperatorKO7 source tree. -/
def leanTheoremIdentifierOf : RDRSMethodFamily → String
  | .standardKBO | .kboWithStatus | .generalizedKBO
      => "OperatorKO7.KBO_Impossible.no_kbo_orients_ko7_rec_succ_trace"
  | .acKBO | .transfiniteKBO | .lambdaFreeKBO
      => "OperatorKO7.RDRSPathOrderDichotomy.kboBarrierVariant_no_symbolic_orientation"
  | .matrixNScalarProjection | .matrixQRScalarProjection | .triangularMatrix
      => "OperatorKO7.MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump"
  | f => OperatorKO7.RDRSCoverageLedger.theoremIdOf f

/-! ## Row builder and the full ledger list -/

/-- Build a single 10-column ledger row from a family. -/
def coverageLedgerRowOf (f : RDRSMethodFamily) : RDRSCoverageLedgerRow :=
  let c := u6ClassOf f
  { family                      := f
    rawConstructor              := rawConstructorOf f
    normalizedCertificate       := normalizedCertificateOf f
    lensTheorem                 := lensTheoremOfClass c
    seedCollapseStatus          := seedCollapseStatusOfClass c
    projectionTransactionStatus := projectionTransactionStatusOf f
    retainedCoordinateStatus    := retainedCoordinateStatusOf f
    classification              := c
    leanTheoremIdentifier       := leanTheoremIdentifierOf f
    paperAClaimSupported        := paperAClaimOfClass c }

/-- The full 76-row coverage ledger, one entry per family. -/
def rdrsFullCoverageLedger : List RDRSCoverageLedgerRow :=
  allMethodFamilies.map coverageLedgerRowOf

/-! ## Bucket extractors (six buckets) -/

/-- Families classified `payloadSensitiveBlocked`. -/
def payloadSensitiveBlockedFamilies : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => u6ClassOf f == .payloadSensitiveBlocked)

/-- Families classified `projectionTransactionEscape`. -/
def projectionTransactionEscapeFamilies : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => u6ClassOf f == .projectionTransactionEscape)

/-- Families classified `constructionEscape`. -/
def constructionEscapeFamilies : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => u6ClassOf f == .constructionEscape)

/-- Families classified `transformEscape`. -/
def transformEscapeFamilies : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => u6ClassOf f == .transformEscape)

/-- Families classified `notDirect`. -/
def notDirectFamiliesU6 : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => u6ClassOf f == .notDirect)

/-- Families classified `temporaryUnclassified`. -/
def temporaryUnclassifiedFamilies : List RDRSMethodFamily :=
  allMethodFamilies.filter (fun f => u6ClassOf f == .temporaryUnclassified)

/-! ## Count theorems (all `decide`-proved) -/

theorem payloadSensitiveBlocked_count :
    payloadSensitiveBlockedFamilies.length = 26 := by decide

theorem projectionTransactionEscape_count :
    projectionTransactionEscapeFamilies.length = 9 := by decide

theorem constructionEscape_count :
    constructionEscapeFamilies.length = 8 := by decide

theorem transformEscape_count :
    transformEscapeFamilies.length = 13 := by decide

theorem notDirect_count_U6 :
    notDirectFamiliesU6.length = 20 := by decide

/-- **Final closeout: the temporary-unclassified bucket is empty.**

The roadmap's mandatory closeout obligation: every family in the 76-row
RDRS universe receives a definite five-way classification; the residual
`temporaryUnclassified` bucket is empty. -/
theorem temporary_unclassified_count :
    temporaryUnclassifiedFamilies.length = 0 := by decide

/-- The six-way classification partitions the 76 rows. -/
theorem u6_partition_total :
    payloadSensitiveBlockedFamilies.length + projectionTransactionEscapeFamilies.length
      + constructionEscapeFamilies.length + transformEscapeFamilies.length
      + notDirectFamiliesU6.length + temporaryUnclassifiedFamilies.length = 76 := by
  decide

/-- The six-way classification is total. -/
theorem u6ClassOf_total (f : RDRSMethodFamily) :
    u6ClassOf f = .payloadSensitiveBlocked
      ∨ u6ClassOf f = .projectionTransactionEscape
      ∨ u6ClassOf f = .constructionEscape
      ∨ u6ClassOf f = .transformEscape
      ∨ u6ClassOf f = .notDirect
      ∨ u6ClassOf f = .temporaryUnclassified := by
  cases f <;> decide

/-- The full ledger has exactly 76 rows. -/
theorem rdrsFullCoverageLedger_length :
    rdrsFullCoverageLedger.length = 76 := by
  simp [rdrsFullCoverageLedger, List.length_map, allMethodFamilies_length]

/-- Every ledger row's classification field agrees with `u6ClassOf`. -/
theorem ledgerRow_classification_correct (f : RDRSMethodFamily) :
    (coverageLedgerRowOf f).classification = u6ClassOf f := rfl

/-- Every ledger row's family field is the family it was built from. -/
theorem ledgerRow_family_correct (f : RDRSMethodFamily) :
    (coverageLedgerRowOf f).family = f := rfl

/-- Every ledger row's Lean theorem identifier matches `leanTheoremIdentifierOf`
on its family by construction. Used by downstream callers to read the
field without re-deriving the lookup. -/
theorem ledgerRow_leanTheoremIdentifier_correct
    (f : RDRSMethodFamily) :
    (coverageLedgerRowOf f).leanTheoremIdentifier
      = leanTheoremIdentifierOf f := rfl

/-! ## Capstone closeout certificate -/

/-- Closeout structure for the U6 coverage ledger. Bundles every closure
obligation the roadmap requires:

1. Six-way classification is total.
2. Each bucket has the exact `decide`-proved count.
3. The buckets partition the 76 rows.
4. The full ledger has 76 rows.
5. Row classification field is correct by construction.
6. **Crucially: the `temporaryUnclassified` bucket is empty.** -/
structure CoverageLedgerClosed : Prop where
  classificationTotal           : ∀ f : RDRSMethodFamily,
    u6ClassOf f = .payloadSensitiveBlocked
      ∨ u6ClassOf f = .projectionTransactionEscape
      ∨ u6ClassOf f = .constructionEscape
      ∨ u6ClassOf f = .transformEscape
      ∨ u6ClassOf f = .notDirect
      ∨ u6ClassOf f = .temporaryUnclassified
  payloadSensitiveBlockedCount  : payloadSensitiveBlockedFamilies.length = 26
  projectionTransactionCount    : projectionTransactionEscapeFamilies.length = 9
  constructionCount             : constructionEscapeFamilies.length = 8
  transformCount                : transformEscapeFamilies.length = 13
  notDirectCount                : notDirectFamiliesU6.length = 20
  temporaryUnclassifiedCount    : temporaryUnclassifiedFamilies.length = 0
  partitionTotal                :
    payloadSensitiveBlockedFamilies.length + projectionTransactionEscapeFamilies.length
      + constructionEscapeFamilies.length + transformEscapeFamilies.length
      + notDirectFamiliesU6.length + temporaryUnclassifiedFamilies.length = 76
  rowCount                      : rdrsFullCoverageLedger.length = 76

/-- **Phase U6 coverage-ledger milestone theorem.**

The U6 coverage ledger is closed: the six-way classification is total on
the 76-family RDRS universe, the buckets partition the rows with the
proved counts, and the `temporaryUnclassified` bucket is empty -- so
every row has a definite classification under the universal payload-
sensitive direct-measure barrier program. -/
theorem rdrs_coverage_ledger_closed : CoverageLedgerClosed where
  classificationTotal           := u6ClassOf_total
  payloadSensitiveBlockedCount  := payloadSensitiveBlocked_count
  projectionTransactionCount    := projectionTransactionEscape_count
  constructionCount             := constructionEscape_count
  transformCount                := transformEscape_count
  notDirectCount                := notDirect_count_U6
  temporaryUnclassifiedCount    := temporary_unclassified_count
  partitionTotal                := u6_partition_total
  rowCount                      := rdrsFullCoverageLedger_length

/-- Audit anchor String for the U6 coverage-ledger milestone. Downstream
registries cite this when wiring the ledger into Paper A's claim index. -/
def rdrs_coverage_ledger_anchor : String :=
  "OperatorKO7.RDRSCoverageLedger.Full.rdrs_coverage_ledger_closed"

end OperatorKO7.RDRSCoverageLedger.Full
