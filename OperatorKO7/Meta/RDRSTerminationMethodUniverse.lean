/-!
# RDRS Termination-Method Universe

Stable enum and status substrate for the RDRS termination-method atlas.

This file intentionally does not prove the family-specific barriers. It fixes
the row names and terminal status vocabulary so parallel closeout files can
share one interface. There is no `open` or unresolved status: every row must
close by a positive classification.
-/

namespace OperatorKO7.RDRSTerminationMethodUniverse

/-- Terminal classification vocabulary for one RDRS method-family row. -/
inductive RDRSMethodStatus
  | barrier
  | conditional_barrier
  | conditional_escape
  | import_dependent
  | definitional_admitter
  | nonconservative_escape
  | not_applicable
  | external_non_lane_problem
  deriving DecidableEq, Repr

/-- Finite row enum for the termination-method universe atlas. -/
inductive RDRSMethodFamily
  -- Path-order layer
  | standardKBO
  | kboWithStatus
  | generalizedKBO
  | subtermCoefficientKBO
  | acKBO
  | transfiniteKBO
  | lambdaFreeKBO
  | acRPO
  | rpoModuloPermutation
  | popStarFamily
  | simpleTerminationOrderType
  | cichonSlowGrowing
  -- Algebraic interpretation layer
  | linearPolyQ
  | linearPolyR
  | negativeCoefficientPolynomial
  | maxPolynomial
  | nonlinearHigherDegreePolynomial
  | multilinearInterpretation
  | matrixNScalarProjection
  | matrixQRScalarProjection
  | arcticScalarProjection
  | tropicalScalarProjection
  | triangularMatrix
  | tupleInterpretationStrictS
  | higherOrderTupleInterpretation
  | polynomialKBO
  -- Semantic and structural layers
  | strictMonotoneAlgebraArchimedean
  | extendedMonotoneAlgebra
  | semanticLabeling
  | predictiveLabeling
  | rootLabeling
  | selfLabelingEquational
  | finiteModelTermination
  | categoricalToposTermination
  | forwardClosures
  | matchBounds
  | raiseConsistencyMatchBounds
  | quasiDecreasingness
  -- Dependency-pair and typed projection layer
  | dpProcessorClassification
  | dpSubtermCriterion
  | dpArgumentFiltering
  | dpReductionPairProcessor
  | dpNeutralProcessors
  | dpReductionTriples
  | usableRulesMinimality
  | formativeRules
  | typeIntroduction
  | manySortedPersistence
  | orderSortedDP
  | contextSensitiveDP
  -- Conditional, constrained, higher-order, and type-based layers
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
  -- Nonconservative and cross-cutting layers
  | sharingNonConservativity
  | weightedTypeGraphEscape
  | generalizedWeightedTypeGraphs
  | equationalQuotientNonConservativity
  | cycleRewritingInapplicability
  | stringRewritingInapplicability
  | leftLinearMatchBounds
  | sizeChangeTerminationEscape
  | infinitaryRewritingTermination
  | piCalculusTerminationTranslation
  | lambdaMuSNViaCPS
  | abstractInterpretationAdmittance
  | quasiInterpretationsSharingAware
  deriving DecidableEq, Repr

/-- Terminal status assigned to each atlas row. -/
def statusOf : RDRSMethodFamily → RDRSMethodStatus
  | .standardKBO => .barrier
  | .kboWithStatus => .barrier
  | .generalizedKBO => .barrier
  | .subtermCoefficientKBO => .conditional_escape
  | .acKBO => .barrier
  | .transfiniteKBO => .barrier
  | .lambdaFreeKBO => .barrier
  | .acRPO => .conditional_escape
  | .rpoModuloPermutation => .conditional_escape
  | .popStarFamily => .conditional_escape
  | .simpleTerminationOrderType => .conditional_barrier
  | .cichonSlowGrowing => .conditional_escape
  | .linearPolyQ => .barrier
  | .linearPolyR => .barrier
  | .negativeCoefficientPolynomial => .conditional_barrier
  | .maxPolynomial => .barrier
  | .nonlinearHigherDegreePolynomial => .conditional_barrier
  | .multilinearInterpretation => .barrier
  | .matrixNScalarProjection => .barrier
  | .matrixQRScalarProjection => .barrier
  | .arcticScalarProjection => .barrier
  | .tropicalScalarProjection => .barrier
  | .triangularMatrix => .barrier
  | .tupleInterpretationStrictS => .conditional_barrier
  | .higherOrderTupleInterpretation => .conditional_barrier
  | .polynomialKBO => .conditional_barrier
  | .strictMonotoneAlgebraArchimedean => .barrier
  | .extendedMonotoneAlgebra => .conditional_barrier
  | .semanticLabeling => .import_dependent
  | .predictiveLabeling => .import_dependent
  | .rootLabeling => .import_dependent
  | .selfLabelingEquational => .import_dependent
  | .finiteModelTermination => .barrier
  | .categoricalToposTermination => .not_applicable
  | .forwardClosures => .not_applicable
  | .matchBounds => .barrier
  | .raiseConsistencyMatchBounds => .barrier
  | .quasiDecreasingness => .import_dependent
  | .dpProcessorClassification => .conditional_escape
  | .dpSubtermCriterion => .conditional_escape
  | .dpArgumentFiltering => .conditional_escape
  | .dpReductionPairProcessor => .import_dependent
  | .dpNeutralProcessors => .not_applicable
  | .dpReductionTriples => .import_dependent
  | .usableRulesMinimality => .conditional_barrier
  | .formativeRules => .not_applicable
  | .typeIntroduction => .conditional_escape
  | .manySortedPersistence => .conditional_escape
  | .orderSortedDP => .conditional_escape
  | .contextSensitiveDP => .conditional_escape
  | .twoDDPForCTRS => .conditional_escape
  | .operationalTerminationCTRS => .import_dependent
  | .integerTermRewriting => .conditional_escape
  | .lctrs => .conditional_escape
  | .higherOrderLCTRS => .conditional_escape
  | .horpoAdmittance => .definitional_admitter
  | .cpoAdmittance => .definitional_admitter
  | .generalSchemaAdmittance => .definitional_admitter
  | .sizedTypesAdmittance => .definitional_admitter
  | .coqGuardAdmittance => .definitional_admitter
  | .bellantoniCookSplit => .conditional_barrier
  | .linearLogicTypingBarrier => .conditional_barrier
  | .ramifiedRecursionTypingBarrier => .conditional_barrier
  | .sharingNonConservativity => .nonconservative_escape
  | .weightedTypeGraphEscape => .nonconservative_escape
  | .generalizedWeightedTypeGraphs => .nonconservative_escape
  | .equationalQuotientNonConservativity => .nonconservative_escape
  | .cycleRewritingInapplicability => .not_applicable
  | .stringRewritingInapplicability => .not_applicable
  | .leftLinearMatchBounds => .conditional_barrier
  | .sizeChangeTerminationEscape => .conditional_escape
  | .infinitaryRewritingTermination => .not_applicable
  | .piCalculusTerminationTranslation => .nonconservative_escape
  | .lambdaMuSNViaCPS => .nonconservative_escape
  | .abstractInterpretationAdmittance => .import_dependent
  | .quasiInterpretationsSharingAware => .nonconservative_escape

/-- Exact finite inventory of all atlas rows. -/
def allMethodFamilies : List RDRSMethodFamily :=
  [ .standardKBO
  , .kboWithStatus
  , .generalizedKBO
  , .subtermCoefficientKBO
  , .acKBO
  , .transfiniteKBO
  , .lambdaFreeKBO
  , .acRPO
  , .rpoModuloPermutation
  , .popStarFamily
  , .simpleTerminationOrderType
  , .cichonSlowGrowing
  , .linearPolyQ
  , .linearPolyR
  , .negativeCoefficientPolynomial
  , .maxPolynomial
  , .nonlinearHigherDegreePolynomial
  , .multilinearInterpretation
  , .matrixNScalarProjection
  , .matrixQRScalarProjection
  , .arcticScalarProjection
  , .tropicalScalarProjection
  , .triangularMatrix
  , .tupleInterpretationStrictS
  , .higherOrderTupleInterpretation
  , .polynomialKBO
  , .strictMonotoneAlgebraArchimedean
  , .extendedMonotoneAlgebra
  , .semanticLabeling
  , .predictiveLabeling
  , .rootLabeling
  , .selfLabelingEquational
  , .finiteModelTermination
  , .categoricalToposTermination
  , .forwardClosures
  , .matchBounds
  , .raiseConsistencyMatchBounds
  , .quasiDecreasingness
  , .dpProcessorClassification
  , .dpSubtermCriterion
  , .dpArgumentFiltering
  , .dpReductionPairProcessor
  , .dpNeutralProcessors
  , .dpReductionTriples
  , .usableRulesMinimality
  , .formativeRules
  , .typeIntroduction
  , .manySortedPersistence
  , .orderSortedDP
  , .contextSensitiveDP
  , .twoDDPForCTRS
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
  , .sharingNonConservativity
  , .weightedTypeGraphEscape
  , .generalizedWeightedTypeGraphs
  , .equationalQuotientNonConservativity
  , .cycleRewritingInapplicability
  , .stringRewritingInapplicability
  , .leftLinearMatchBounds
  , .sizeChangeTerminationEscape
  , .infinitaryRewritingTermination
  , .piCalculusTerminationTranslation
  , .lambdaMuSNViaCPS
  , .abstractInterpretationAdmittance
  , .quasiInterpretationsSharingAware
  ]

theorem allMethodFamilies_nodup : allMethodFamilies.Nodup := by decide

theorem allMethodFamilies_length : allMethodFamilies.length = 76 := by decide

theorem allMethodFamilies_complete :
    ∀ family : RDRSMethodFamily, family ∈ allMethodFamilies := by
  intro family
  cases family <;> decide

/-- Every row has a terminal status by construction. -/
theorem statusOf_terminal (family : RDRSMethodFamily) :
    ∃ status : RDRSMethodStatus, statusOf family = status :=
  ⟨statusOf family, rfl⟩

end OperatorKO7.RDRSTerminationMethodUniverse
