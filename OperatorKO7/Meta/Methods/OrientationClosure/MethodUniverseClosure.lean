import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsKBO
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsPathOrders
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsInterpretations
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsDependencyPairs
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsUsableFormative
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSubstrate
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsLabelingBounds
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSortedConstrained
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsConditionalConstrained
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsTypedCalculi
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsTypingDisciplines
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsGraphCalculi
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsProcessCalculi
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSemanticFrameworks
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsOtherCalculi
import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# Method row-contract closure

Every one of the 76 catalogue rows has data, laws, and a proved row result on the free recursor
(`method_universe_closure`). Thirteen formerly unresolved named-method rows also carry exact
source-level method-identity theorems in `namedMethodIdentity`. The covered list is built from the
certificates and equals `allMethodFamilies` (`coveredRows_eq`); removing one certificate breaks the
equality (`coverage_mutation`). Every row carries its soundness or universal theorem (`methodSound`)
and its mutation control (`methodMutation`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace OperatorKO7.Methods.OrientationClosure.MethodUniverseClosure

open OperatorKO7.RDRSTerminationMethodUniverse

/-- Verdict of a row on the free recursor. -/
inductive MethodVerdict where
  | barrier
  | escape
  | fragmentBarrier
  | fragmentEscape
  deriving DecidableEq, Repr

/-- Native data of each row. -/
def MethodData : RDRSMethodFamily → Type 2
  | .standardKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOData
  | .kboWithStatus => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusData
  | .generalizedKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOData
  | .subtermCoefficientKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOData
  | .acKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOData
  | .transfiniteKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOData
  | .lambdaFreeKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOData
  | .acRPO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOData
  | .rpoModuloPermutation => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationData
  | .popStarFamily => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyData
  | .simpleTerminationOrderType => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeData
  | .cichonSlowGrowing => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingData
  | .linearPolyQ => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQData
  | .linearPolyR => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRData
  | .negativeCoefficientPolynomial => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialData
  | .maxPolynomial => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialData
  | .nonlinearHigherDegreePolynomial => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialData
  | .multilinearInterpretation => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationData
  | .matrixNScalarProjection => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionData
  | .matrixQRScalarProjection => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionData
  | .arcticScalarProjection => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionData
  | .tropicalScalarProjection => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionData
  | .triangularMatrix => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixData
  | .tupleInterpretationStrictS => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSData
  | .higherOrderTupleInterpretation => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationData
  | .polynomialKBO => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOData
  | .strictMonotoneAlgebraArchimedean => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanData
  | .extendedMonotoneAlgebra => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraData
  | .semanticLabeling => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingData
  | .predictiveLabeling => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingData
  | .rootLabeling => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingData
  | .selfLabelingEquational => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalData
  | .finiteModelTermination => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationData
  | .categoricalToposTermination => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationData
  | .forwardClosures => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresData
  | .matchBounds => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsData
  | .raiseConsistencyMatchBounds => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsData
  | .quasiDecreasingness => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessData
  | .dpProcessorClassification => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationData
  | .dpSubtermCriterion => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionData
  | .dpArgumentFiltering => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringData
  | .dpReductionPairProcessor => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorData
  | .dpNeutralProcessors => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsData
  | .dpReductionTriples => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesData
  | .usableRulesMinimality => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityData
  | .formativeRules => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesData
  | .typeIntroduction => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionData
  | .manySortedPersistence => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceData
  | .orderSortedDP => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPData
  | .contextSensitiveDP => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPData
  | .twoDDPForCTRS => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSData
  | .operationalTerminationCTRS => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSData
  | .integerTermRewriting => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingData
  | .lctrs => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsData
  | .higherOrderLCTRS => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSData
  | .horpoAdmittance => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceData
  | .cpoAdmittance => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceData
  | .generalSchemaAdmittance => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceData
  | .sizedTypesAdmittance => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceData
  | .coqGuardAdmittance => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceData
  | .bellantoniCookSplit => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitData
  | .linearLogicTypingBarrier => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierData
  | .ramifiedRecursionTypingBarrier => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierData
  | .sharingNonConservativity => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityData
  | .weightedTypeGraphEscape => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeData
  | .generalizedWeightedTypeGraphs => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsData
  | .equationalQuotientNonConservativity => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityData
  | .cycleRewritingInapplicability => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityData
  | .stringRewritingInapplicability => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityData
  | .leftLinearMatchBounds => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsData
  | .sizeChangeTerminationEscape => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeData
  | .infinitaryRewritingTermination => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationData
  | .piCalculusTerminationTranslation => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationData
  | .lambdaMuSNViaCPS => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSData
  | .abstractInterpretationAdmittance => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceData
  | .quasiInterpretationsSharingAware => ULift.{2} OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareData

/-- Laws of each row. -/
def MethodLaws : (f : RDRSMethodFamily) → MethodData f → Prop
  | .standardKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOLaws M.down
  | .kboWithStatus => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusLaws M.down
  | .generalizedKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOLaws M.down
  | .subtermCoefficientKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOLaws M.down
  | .acKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOLaws M.down
  | .transfiniteKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOLaws M.down
  | .lambdaFreeKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOLaws M.down
  | .acRPO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOLaws M.down
  | .rpoModuloPermutation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationLaws M.down
  | .popStarFamily => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyLaws M.down
  | .simpleTerminationOrderType => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeLaws M.down
  | .cichonSlowGrowing => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingLaws M.down
  | .linearPolyQ => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQLaws M.down
  | .linearPolyR => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRLaws M.down
  | .negativeCoefficientPolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialLaws M.down
  | .maxPolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialLaws M.down
  | .nonlinearHigherDegreePolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialLaws M.down
  | .multilinearInterpretation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationLaws M.down
  | .matrixNScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionLaws M.down
  | .matrixQRScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionLaws M.down
  | .arcticScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionLaws M.down
  | .tropicalScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionLaws M.down
  | .triangularMatrix => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixLaws M.down
  | .tupleInterpretationStrictS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSLaws M.down
  | .higherOrderTupleInterpretation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationLaws M.down
  | .polynomialKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOLaws M.down
  | .strictMonotoneAlgebraArchimedean => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanLaws M.down
  | .extendedMonotoneAlgebra => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraLaws M.down
  | .semanticLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingLaws M.down
  | .predictiveLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingLaws M.down
  | .rootLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingLaws M.down
  | .selfLabelingEquational => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalLaws M.down
  | .finiteModelTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationLaws M.down
  | .categoricalToposTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationLaws M.down
  | .forwardClosures => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresLaws M.down
  | .matchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsLaws M.down
  | .raiseConsistencyMatchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsLaws M.down
  | .quasiDecreasingness => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessLaws M.down
  | .dpProcessorClassification => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationLaws M.down
  | .dpSubtermCriterion => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionLaws M.down
  | .dpArgumentFiltering => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringLaws M.down
  | .dpReductionPairProcessor => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorLaws M.down
  | .dpNeutralProcessors => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsLaws M.down
  | .dpReductionTriples => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesLaws M.down
  | .usableRulesMinimality => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityLaws M.down
  | .formativeRules => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesLaws M.down
  | .typeIntroduction => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionLaws M.down
  | .manySortedPersistence => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceLaws M.down
  | .orderSortedDP => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPLaws M.down
  | .contextSensitiveDP => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPLaws M.down
  | .twoDDPForCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSLaws M.down
  | .operationalTerminationCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSLaws M.down
  | .integerTermRewriting => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingLaws M.down
  | .lctrs => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsLaws M.down
  | .higherOrderLCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSLaws M.down
  | .horpoAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceLaws M.down
  | .cpoAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceLaws M.down
  | .generalSchemaAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceLaws M.down
  | .sizedTypesAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceLaws M.down
  | .coqGuardAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceLaws M.down
  | .bellantoniCookSplit => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitLaws M.down
  | .linearLogicTypingBarrier => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierLaws M.down
  | .ramifiedRecursionTypingBarrier => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierLaws M.down
  | .sharingNonConservativity => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityLaws M.down
  | .weightedTypeGraphEscape => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeLaws M.down
  | .generalizedWeightedTypeGraphs => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsLaws M.down
  | .equationalQuotientNonConservativity => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityLaws M.down
  | .cycleRewritingInapplicability => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityLaws M.down
  | .stringRewritingInapplicability => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityLaws M.down
  | .leftLinearMatchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsLaws M.down
  | .sizeChangeTerminationEscape => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeLaws M.down
  | .infinitaryRewritingTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationLaws M.down
  | .piCalculusTerminationTranslation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationLaws M.down
  | .lambdaMuSNViaCPS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSLaws M.down
  | .abstractInterpretationAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceLaws M.down
  | .quasiInterpretationsSharingAware => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareLaws M.down

/-- Acceptance of the free duplicating rule by each row. -/
def MethodAccepts : (f : RDRSMethodFamily) → MethodData f → Prop
  | .standardKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOAccepts M.down
  | .kboWithStatus => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusAccepts M.down
  | .generalizedKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOAccepts M.down
  | .subtermCoefficientKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOAccepts M.down
  | .acKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOAccepts M.down
  | .transfiniteKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOAccepts M.down
  | .lambdaFreeKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOAccepts M.down
  | .acRPO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOAccepts M.down
  | .rpoModuloPermutation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationAccepts M.down
  | .popStarFamily => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyAccepts M.down
  | .simpleTerminationOrderType => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeAccepts M.down
  | .cichonSlowGrowing => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingAccepts M.down
  | .linearPolyQ => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQAccepts M.down
  | .linearPolyR => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRAccepts M.down
  | .negativeCoefficientPolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialAccepts M.down
  | .maxPolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialAccepts M.down
  | .nonlinearHigherDegreePolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialAccepts M.down
  | .multilinearInterpretation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationAccepts M.down
  | .matrixNScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionAccepts M.down
  | .matrixQRScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionAccepts M.down
  | .arcticScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionAccepts M.down
  | .tropicalScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionAccepts M.down
  | .triangularMatrix => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixAccepts M.down
  | .tupleInterpretationStrictS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSAccepts M.down
  | .higherOrderTupleInterpretation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationAccepts M.down
  | .polynomialKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOAccepts M.down
  | .strictMonotoneAlgebraArchimedean => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanAccepts M.down
  | .extendedMonotoneAlgebra => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraAccepts M.down
  | .semanticLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingAccepts M.down
  | .predictiveLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingAccepts M.down
  | .rootLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingAccepts M.down
  | .selfLabelingEquational => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalAccepts M.down
  | .finiteModelTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationAccepts M.down
  | .categoricalToposTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationAccepts M.down
  | .forwardClosures => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresAccepts M.down
  | .matchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsAccepts M.down
  | .raiseConsistencyMatchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsAccepts M.down
  | .quasiDecreasingness => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessAccepts M.down
  | .dpProcessorClassification => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationAccepts M.down
  | .dpSubtermCriterion => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionAccepts M.down
  | .dpArgumentFiltering => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringAccepts M.down
  | .dpReductionPairProcessor => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorAccepts M.down
  | .dpNeutralProcessors => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsAccepts M.down
  | .dpReductionTriples => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesAccepts M.down
  | .usableRulesMinimality => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityAccepts M.down
  | .formativeRules => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesAccepts M.down
  | .typeIntroduction => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionAccepts M.down
  | .manySortedPersistence => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceAccepts M.down
  | .orderSortedDP => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPAccepts M.down
  | .contextSensitiveDP => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPAccepts M.down
  | .twoDDPForCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSAccepts M.down
  | .operationalTerminationCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSAccepts M.down
  | .integerTermRewriting => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingAccepts M.down
  | .lctrs => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsAccepts M.down
  | .higherOrderLCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSAccepts M.down
  | .horpoAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceAccepts M.down
  | .cpoAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceAccepts M.down
  | .generalSchemaAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceAccepts M.down
  | .sizedTypesAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceAccepts M.down
  | .coqGuardAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceAccepts M.down
  | .bellantoniCookSplit => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitAccepts M.down
  | .linearLogicTypingBarrier => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierAccepts M.down
  | .ramifiedRecursionTypingBarrier => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierAccepts M.down
  | .sharingNonConservativity => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityAccepts M.down
  | .weightedTypeGraphEscape => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeAccepts M.down
  | .generalizedWeightedTypeGraphs => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsAccepts M.down
  | .equationalQuotientNonConservativity => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityAccepts M.down
  | .cycleRewritingInapplicability => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityAccepts M.down
  | .stringRewritingInapplicability => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityAccepts M.down
  | .leftLinearMatchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsAccepts M.down
  | .sizeChangeTerminationEscape => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeAccepts M.down
  | .infinitaryRewritingTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationAccepts M.down
  | .piCalculusTerminationTranslation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationAccepts M.down
  | .lambdaMuSNViaCPS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSAccepts M.down
  | .abstractInterpretationAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceAccepts M.down
  | .quasiInterpretationsSharingAware => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareAccepts M.down

/-- Result of each row on the free recursor. -/
def MethodResult : (f : RDRSMethodFamily) → MethodData f → Prop
  | .standardKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOResult M.down
  | .kboWithStatus => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusResult M.down
  | .generalizedKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOResult M.down
  | .subtermCoefficientKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOResult M.down
  | .acKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOResult M.down
  | .transfiniteKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOResult M.down
  | .lambdaFreeKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOResult M.down
  | .acRPO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOResult M.down
  | .rpoModuloPermutation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationResult M.down
  | .popStarFamily => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyResult M.down
  | .simpleTerminationOrderType => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeResult M.down
  | .cichonSlowGrowing => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingResult M.down
  | .linearPolyQ => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQResult M.down
  | .linearPolyR => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRResult M.down
  | .negativeCoefficientPolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialResult M.down
  | .maxPolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialResult M.down
  | .nonlinearHigherDegreePolynomial => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialResult M.down
  | .multilinearInterpretation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationResult M.down
  | .matrixNScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionResult M.down
  | .matrixQRScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionResult M.down
  | .arcticScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionResult M.down
  | .tropicalScalarProjection => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionResult M.down
  | .triangularMatrix => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixResult M.down
  | .tupleInterpretationStrictS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSResult M.down
  | .higherOrderTupleInterpretation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationResult M.down
  | .polynomialKBO => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOResult M.down
  | .strictMonotoneAlgebraArchimedean => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanResult M.down
  | .extendedMonotoneAlgebra => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraResult M.down
  | .semanticLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingResult M.down
  | .predictiveLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingResult M.down
  | .rootLabeling => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingResult M.down
  | .selfLabelingEquational => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalResult M.down
  | .finiteModelTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationResult M.down
  | .categoricalToposTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationResult M.down
  | .forwardClosures => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresResult M.down
  | .matchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsResult M.down
  | .raiseConsistencyMatchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsResult M.down
  | .quasiDecreasingness => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessResult M.down
  | .dpProcessorClassification => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationResult M.down
  | .dpSubtermCriterion => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionResult M.down
  | .dpArgumentFiltering => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringResult M.down
  | .dpReductionPairProcessor => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorResult M.down
  | .dpNeutralProcessors => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsResult M.down
  | .dpReductionTriples => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesResult M.down
  | .usableRulesMinimality => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityResult M.down
  | .formativeRules => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesResult M.down
  | .typeIntroduction => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionResult M.down
  | .manySortedPersistence => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceResult M.down
  | .orderSortedDP => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPResult M.down
  | .contextSensitiveDP => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPResult M.down
  | .twoDDPForCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSResult M.down
  | .operationalTerminationCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSResult M.down
  | .integerTermRewriting => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingResult M.down
  | .lctrs => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsResult M.down
  | .higherOrderLCTRS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSResult M.down
  | .horpoAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceResult M.down
  | .cpoAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceResult M.down
  | .generalSchemaAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceResult M.down
  | .sizedTypesAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceResult M.down
  | .coqGuardAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceResult M.down
  | .bellantoniCookSplit => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitResult M.down
  | .linearLogicTypingBarrier => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierResult M.down
  | .ramifiedRecursionTypingBarrier => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierResult M.down
  | .sharingNonConservativity => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityResult M.down
  | .weightedTypeGraphEscape => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeResult M.down
  | .generalizedWeightedTypeGraphs => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsResult M.down
  | .equationalQuotientNonConservativity => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityResult M.down
  | .cycleRewritingInapplicability => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityResult M.down
  | .stringRewritingInapplicability => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityResult M.down
  | .leftLinearMatchBounds => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsResult M.down
  | .sizeChangeTerminationEscape => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeResult M.down
  | .infinitaryRewritingTermination => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationResult M.down
  | .piCalculusTerminationTranslation => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationResult M.down
  | .lambdaMuSNViaCPS => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSResult M.down
  | .abstractInterpretationAdmittance => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceResult M.down
  | .quasiInterpretationsSharingAware => fun M => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareResult M.down

/-- Verdict of each row. -/
def methodVerdict : RDRSMethodFamily → MethodVerdict
  | .standardKBO => .barrier
  | .kboWithStatus => .barrier
  | .generalizedKBO => .escape
  | .subtermCoefficientKBO => .barrier
  | .acKBO => .barrier
  | .transfiniteKBO => .barrier
  | .lambdaFreeKBO => .barrier
  | .acRPO => .escape
  | .rpoModuloPermutation => .escape
  | .popStarFamily => .escape
  | .simpleTerminationOrderType => .escape
  | .cichonSlowGrowing => .escape
  | .linearPolyQ => .barrier
  | .linearPolyR => .barrier
  | .negativeCoefficientPolynomial => .escape
  | .maxPolynomial => .escape
  | .nonlinearHigherDegreePolynomial => .escape
  | .multilinearInterpretation => .escape
  | .matrixNScalarProjection => .barrier
  | .matrixQRScalarProjection => .barrier
  | .arcticScalarProjection => .barrier
  | .tropicalScalarProjection => .barrier
  | .triangularMatrix => .barrier
  | .tupleInterpretationStrictS => .escape
  | .higherOrderTupleInterpretation => .escape
  | .polynomialKBO => .escape
  | .strictMonotoneAlgebraArchimedean => .escape
  | .extendedMonotoneAlgebra => .escape
  | .semanticLabeling => .escape
  | .predictiveLabeling => .escape
  | .rootLabeling => .escape
  | .selfLabelingEquational => .escape
  | .finiteModelTermination => .barrier
  | .categoricalToposTermination => .escape
  | .forwardClosures => .barrier
  | .matchBounds => .barrier
  | .raiseConsistencyMatchBounds => .escape
  | .quasiDecreasingness => .escape
  | .dpProcessorClassification => .escape
  | .dpSubtermCriterion => .escape
  | .dpArgumentFiltering => .escape
  | .dpReductionPairProcessor => .escape
  | .dpNeutralProcessors => .escape
  | .dpReductionTriples => .escape
  | .usableRulesMinimality => .fragmentEscape
  | .formativeRules => .escape
  | .typeIntroduction => .barrier
  | .manySortedPersistence => .escape
  | .orderSortedDP => .escape
  | .contextSensitiveDP => .escape
  | .twoDDPForCTRS => .escape
  | .operationalTerminationCTRS => .escape
  | .integerTermRewriting => .escape
  | .lctrs => .escape
  | .higherOrderLCTRS => .escape
  | .horpoAdmittance => .fragmentEscape
  | .cpoAdmittance => .fragmentEscape
  | .generalSchemaAdmittance => .fragmentEscape
  | .sizedTypesAdmittance => .fragmentEscape
  | .coqGuardAdmittance => .fragmentEscape
  | .bellantoniCookSplit => .fragmentEscape
  | .linearLogicTypingBarrier => .fragmentBarrier
  | .ramifiedRecursionTypingBarrier => .fragmentEscape
  | .sharingNonConservativity => .escape
  | .weightedTypeGraphEscape => .escape
  | .generalizedWeightedTypeGraphs => .escape
  | .equationalQuotientNonConservativity => .escape
  | .cycleRewritingInapplicability => .barrier
  | .stringRewritingInapplicability => .barrier
  | .leftLinearMatchBounds => .barrier
  | .sizeChangeTerminationEscape => .escape
  | .infinitaryRewritingTermination => .fragmentEscape
  | .piCalculusTerminationTranslation => .escape
  | .lambdaMuSNViaCPS => .escape
  | .abstractInterpretationAdmittance => .escape
  | .quasiInterpretationsSharingAware => .escape

/-- Witness data of each row. -/
noncomputable def methodWitness : (f : RDRSMethodFamily) → MethodData f
  | .standardKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOWitness
  | .kboWithStatus => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusWitness
  | .generalizedKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOWitness
  | .subtermCoefficientKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOWitness
  | .acKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOWitness
  | .transfiniteKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOWitness
  | .lambdaFreeKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOWitness
  | .acRPO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOWitness
  | .rpoModuloPermutation => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationWitness
  | .popStarFamily => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyWitness
  | .simpleTerminationOrderType => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeWitness
  | .cichonSlowGrowing => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingWitness
  | .linearPolyQ => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQWitness
  | .linearPolyR => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRWitness
  | .negativeCoefficientPolynomial => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialWitness
  | .maxPolynomial => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialWitness
  | .nonlinearHigherDegreePolynomial => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialWitness
  | .multilinearInterpretation => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationWitness
  | .matrixNScalarProjection => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionWitness
  | .matrixQRScalarProjection => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionWitness
  | .arcticScalarProjection => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionWitness
  | .tropicalScalarProjection => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionWitness
  | .triangularMatrix => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixWitness
  | .tupleInterpretationStrictS => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSWitness
  | .higherOrderTupleInterpretation => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness
  | .polynomialKBO => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOWitness
  | .strictMonotoneAlgebraArchimedean => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanWitness
  | .extendedMonotoneAlgebra => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraWitness
  | .semanticLabeling => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingWitness
  | .predictiveLabeling => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingWitness
  | .rootLabeling => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingWitness
  | .selfLabelingEquational => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalWitness
  | .finiteModelTermination => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationWitness
  | .categoricalToposTermination => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationWitness
  | .forwardClosures => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresWitness
  | .matchBounds => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsWitness
  | .raiseConsistencyMatchBounds => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsWitness
  | .quasiDecreasingness => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessWitness
  | .dpProcessorClassification => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationWitness
  | .dpSubtermCriterion => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionWitness
  | .dpArgumentFiltering => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringWitness
  | .dpReductionPairProcessor => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorWitness
  | .dpNeutralProcessors => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsWitness
  | .dpReductionTriples => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesWitness
  | .usableRulesMinimality => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityWitness
  | .formativeRules => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesWitness
  | .typeIntroduction => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionWitness
  | .manySortedPersistence => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceWitness
  | .orderSortedDP => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPWitness
  | .contextSensitiveDP => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPWitness
  | .twoDDPForCTRS => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSWitness
  | .operationalTerminationCTRS => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSWitness
  | .integerTermRewriting => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingWitness
  | .lctrs => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsWitness
  | .higherOrderLCTRS => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSWitness
  | .horpoAdmittance => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceWitness
  | .cpoAdmittance => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceWitness
  | .generalSchemaAdmittance => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceWitness
  | .sizedTypesAdmittance => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceWitness
  | .coqGuardAdmittance => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceWitness
  | .bellantoniCookSplit => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitWitness
  | .linearLogicTypingBarrier => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierWitness
  | .ramifiedRecursionTypingBarrier => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierWitness
  | .sharingNonConservativity => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityWitness
  | .weightedTypeGraphEscape => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeWitness
  | .generalizedWeightedTypeGraphs => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsWitness
  | .equationalQuotientNonConservativity => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityWitness
  | .cycleRewritingInapplicability => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityWitness
  | .stringRewritingInapplicability => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityWitness
  | .leftLinearMatchBounds => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsWitness
  | .sizeChangeTerminationEscape => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeWitness
  | .infinitaryRewritingTermination => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness
  | .piCalculusTerminationTranslation => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationWitness
  | .lambdaMuSNViaCPS => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSWitness
  | .abstractInterpretationAdmittance => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceWitness
  | .quasiInterpretationsSharingAware => ULift.up OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareWitness

theorem methodWitness_laws : ∀ f, MethodLaws f (methodWitness f)
  | .standardKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOWitness_laws
  | .kboWithStatus => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusWitness_laws
  | .generalizedKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOWitness_laws
  | .subtermCoefficientKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOWitness_laws
  | .acKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOWitness_laws
  | .transfiniteKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOWitness_laws
  | .lambdaFreeKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOWitness_laws
  | .acRPO => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOWitness_laws
  | .rpoModuloPermutation => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationWitness_laws
  | .popStarFamily => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyWitness_laws
  | .simpleTerminationOrderType => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeWitness_laws
  | .cichonSlowGrowing => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingWitness_laws
  | .linearPolyQ => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQWitness_laws
  | .linearPolyR => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRWitness_laws
  | .negativeCoefficientPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialWitness_laws
  | .maxPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialWitness_laws
  | .nonlinearHigherDegreePolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialWitness_laws
  | .multilinearInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationWitness_laws
  | .matrixNScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionWitness_laws
  | .matrixQRScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionWitness_laws
  | .arcticScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionWitness_laws
  | .tropicalScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionWitness_laws
  | .triangularMatrix => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixWitness_laws
  | .tupleInterpretationStrictS => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSWitness_laws
  | .higherOrderTupleInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness_laws
  | .polynomialKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOWitness_laws
  | .strictMonotoneAlgebraArchimedean => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanWitness_laws
  | .extendedMonotoneAlgebra => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraWitness_laws
  | .semanticLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingWitness_laws
  | .predictiveLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingWitness_laws
  | .rootLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingWitness_laws
  | .selfLabelingEquational => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalWitness_laws
  | .finiteModelTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationWitness_laws
  | .categoricalToposTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationWitness_laws
  | .forwardClosures => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresWitness_laws
  | .matchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsWitness_laws
  | .raiseConsistencyMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsWitness_laws
  | .quasiDecreasingness => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessWitness_laws
  | .dpProcessorClassification => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationWitness_laws
  | .dpSubtermCriterion => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionWitness_laws
  | .dpArgumentFiltering => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringWitness_laws
  | .dpReductionPairProcessor => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorWitness_laws
  | .dpNeutralProcessors => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsWitness_laws
  | .dpReductionTriples => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesWitness_laws
  | .usableRulesMinimality => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityWitness_laws
  | .formativeRules => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesWitness_laws
  | .typeIntroduction => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionWitness_laws
  | .manySortedPersistence => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceWitness_laws
  | .orderSortedDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPWitness_laws
  | .contextSensitiveDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPWitness_laws
  | .twoDDPForCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSWitness_laws
  | .operationalTerminationCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSWitness_laws
  | .integerTermRewriting => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingWitness_laws
  | .lctrs => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsWitness_laws
  | .higherOrderLCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSWitness_laws
  | .horpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceWitness_laws
  | .cpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceWitness_laws
  | .generalSchemaAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceWitness_laws
  | .sizedTypesAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceWitness_laws
  | .coqGuardAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceWitness_laws
  | .bellantoniCookSplit => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitWitness_laws
  | .linearLogicTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierWitness_laws
  | .ramifiedRecursionTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierWitness_laws
  | .sharingNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityWitness_laws
  | .weightedTypeGraphEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeWitness_laws
  | .generalizedWeightedTypeGraphs => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsWitness_laws
  | .equationalQuotientNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityWitness_laws
  | .cycleRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityWitness_laws
  | .stringRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityWitness_laws
  | .leftLinearMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsWitness_laws
  | .sizeChangeTerminationEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeWitness_laws
  | .infinitaryRewritingTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness_laws
  | .piCalculusTerminationTranslation => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationWitness_laws
  | .lambdaMuSNViaCPS => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSWitness_laws
  | .abstractInterpretationAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceWitness_laws
  | .quasiInterpretationsSharingAware => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareWitness_laws

theorem methodWitness_result : ∀ f, MethodResult f (methodWitness f)
  | .standardKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOWitness_result
  | .kboWithStatus => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusWitness_result
  | .generalizedKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOWitness_result
  | .subtermCoefficientKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOWitness_result
  | .acKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOWitness_result
  | .transfiniteKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOWitness_result
  | .lambdaFreeKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOWitness_result
  | .acRPO => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOWitness_result
  | .rpoModuloPermutation => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationWitness_result
  | .popStarFamily => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyWitness_result
  | .simpleTerminationOrderType => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeWitness_result
  | .cichonSlowGrowing => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingWitness_result
  | .linearPolyQ => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQWitness_result
  | .linearPolyR => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRWitness_result
  | .negativeCoefficientPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialWitness_result
  | .maxPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialWitness_result
  | .nonlinearHigherDegreePolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialWitness_result
  | .multilinearInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationWitness_result
  | .matrixNScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionWitness_result
  | .matrixQRScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionWitness_result
  | .arcticScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionWitness_result
  | .tropicalScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionWitness_result
  | .triangularMatrix => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixWitness_result
  | .tupleInterpretationStrictS => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSWitness_result
  | .higherOrderTupleInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness_result
  | .polynomialKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOWitness_result
  | .strictMonotoneAlgebraArchimedean => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanWitness_result
  | .extendedMonotoneAlgebra => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraWitness_result
  | .semanticLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingWitness_result
  | .predictiveLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingWitness_result
  | .rootLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingWitness_result
  | .selfLabelingEquational => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalWitness_result
  | .finiteModelTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationWitness_result
  | .categoricalToposTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationWitness_result
  | .forwardClosures => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresWitness_result
  | .matchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsWitness_result
  | .raiseConsistencyMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsWitness_result
  | .quasiDecreasingness => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessWitness_result
  | .dpProcessorClassification => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationWitness_result
  | .dpSubtermCriterion => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionWitness_result
  | .dpArgumentFiltering => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringWitness_result
  | .dpReductionPairProcessor => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorWitness_result
  | .dpNeutralProcessors => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsWitness_result
  | .dpReductionTriples => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesWitness_result
  | .usableRulesMinimality => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityWitness_result
  | .formativeRules => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesWitness_result
  | .typeIntroduction => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionWitness_result
  | .manySortedPersistence => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceWitness_result
  | .orderSortedDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPWitness_result
  | .contextSensitiveDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPWitness_result
  | .twoDDPForCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSWitness_result
  | .operationalTerminationCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSWitness_result
  | .integerTermRewriting => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingWitness_result
  | .lctrs => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsWitness_result
  | .higherOrderLCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSWitness_result
  | .horpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceWitness_result
  | .cpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceWitness_result
  | .generalSchemaAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceWitness_result
  | .sizedTypesAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceWitness_result
  | .coqGuardAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceWitness_result
  | .bellantoniCookSplit => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitWitness_result
  | .linearLogicTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierWitness_result
  | .ramifiedRecursionTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierWitness_result
  | .sharingNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityWitness_result
  | .weightedTypeGraphEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeWitness_result
  | .generalizedWeightedTypeGraphs => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsWitness_result
  | .equationalQuotientNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityWitness_result
  | .cycleRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityWitness_result
  | .stringRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityWitness_result
  | .leftLinearMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsWitness_result
  | .sizeChangeTerminationEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeWitness_result
  | .infinitaryRewritingTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness_result
  | .piCalculusTerminationTranslation => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationWitness_result
  | .lambdaMuSNViaCPS => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSWitness_result
  | .abstractInterpretationAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceWitness_result
  | .quasiInterpretationsSharingAware => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareWitness_result

/-- The universal or soundness theorem of each row, as stated in its module. -/
def MethodSound : RDRSMethodFamily → Prop
  | .standardKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBO_universal
  | .kboWithStatus => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatus_universal
  | .generalizedKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBO_sound
  | .subtermCoefficientKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBO_universal
  | .acKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBO_universal
  | .transfiniteKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBO_universal
  | .lambdaFreeKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBO_universal
  | .acRPO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPO_sound
  | .rpoModuloPermutation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutation_sound
  | .popStarFamily => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamily_sound
  | .simpleTerminationOrderType => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderType_sound
  | .cichonSlowGrowing => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowing_sound
  | .linearPolyQ => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQ_universal
  | .linearPolyR => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyR_universal
  | .negativeCoefficientPolynomial => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomial_sound
  | .maxPolynomial => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomial_sound
  | .nonlinearHigherDegreePolynomial => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomial_sound
  | .multilinearInterpretation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretation_sound
  | .matrixNScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjection_universal
  | .matrixQRScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjection_universal
  | .arcticScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjection_universal
  | .tropicalScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjection_universal
  | .triangularMatrix => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrix_universal
  | .tupleInterpretationStrictS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictS_sound
  | .higherOrderTupleInterpretation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretation_sound
  | .polynomialKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBO_sound
  | .strictMonotoneAlgebraArchimedean => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedean_sound
  | .extendedMonotoneAlgebra => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebra_sound
  | .semanticLabeling => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabeling_sound
  | .predictiveLabeling => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabeling_sound
  | .rootLabeling => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabeling_sound
  | .selfLabelingEquational => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquational_sound
  | .finiteModelTermination => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTermination_universal
  | .categoricalToposTermination => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTermination_sound
  | .forwardClosures => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosures_universal
  | .matchBounds => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBounds_universal
  | .raiseConsistencyMatchBounds => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBounds_sound
  | .quasiDecreasingness => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingness_sound
  | .dpProcessorClassification => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassification_sound
  | .dpSubtermCriterion => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterion_sound
  | .dpArgumentFiltering => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFiltering_sound
  | .dpReductionPairProcessor => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessor_sound
  | .dpNeutralProcessors => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessors_sound
  | .dpReductionTriples => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriples_sound
  | .usableRulesMinimality => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimality_sound
  | .formativeRules => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRules_sound
  | .typeIntroduction => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroduction_universal
  | .manySortedPersistence => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistence_sound
  | .orderSortedDP => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDP_sound
  | .contextSensitiveDP => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDP_sound
  | .twoDDPForCTRS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRS_sound
  | .operationalTerminationCTRS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRS_sound
  | .integerTermRewriting => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewriting_sound
  | .lctrs => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrs_sound
  | .higherOrderLCTRS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRS_sound
  | .horpoAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittance_sound
  | .cpoAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittance_sound
  | .generalSchemaAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittance_sound
  | .sizedTypesAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittance_sound
  | .coqGuardAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittance_sound
  | .bellantoniCookSplit => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplit_sound
  | .linearLogicTypingBarrier => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrier_universal
  | .ramifiedRecursionTypingBarrier => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrier_sound
  | .sharingNonConservativity => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativity_universal
  | .weightedTypeGraphEscape => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscape_sound
  | .generalizedWeightedTypeGraphs => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphs_sound
  | .equationalQuotientNonConservativity => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativity_sound
  | .cycleRewritingInapplicability => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicability_universal
  | .stringRewritingInapplicability => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicability_universal
  | .leftLinearMatchBounds => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBounds_universal
  | .sizeChangeTerminationEscape => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscape_sound
  | .infinitaryRewritingTermination => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTermination_sound
  | .piCalculusTerminationTranslation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslation_sound
  | .lambdaMuSNViaCPS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPS_sound
  | .abstractInterpretationAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittance_sound
  | .quasiInterpretationsSharingAware => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAware_sound

theorem methodSound : ∀ f, MethodSound f
  | .standardKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBO_universal
  | .kboWithStatus => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatus_universal
  | .generalizedKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBO_sound
  | .subtermCoefficientKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBO_universal
  | .acKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBO_universal
  | .transfiniteKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBO_universal
  | .lambdaFreeKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBO_universal
  | .acRPO => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPO_sound
  | .rpoModuloPermutation => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutation_sound
  | .popStarFamily => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamily_sound
  | .simpleTerminationOrderType => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderType_sound
  | .cichonSlowGrowing => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowing_sound
  | .linearPolyQ => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQ_universal
  | .linearPolyR => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyR_universal
  | .negativeCoefficientPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomial_sound
  | .maxPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomial_sound
  | .nonlinearHigherDegreePolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomial_sound
  | .multilinearInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretation_sound
  | .matrixNScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjection_universal
  | .matrixQRScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjection_universal
  | .arcticScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjection_universal
  | .tropicalScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjection_universal
  | .triangularMatrix => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrix_universal
  | .tupleInterpretationStrictS => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictS_sound
  | .higherOrderTupleInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretation_sound
  | .polynomialKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBO_sound
  | .strictMonotoneAlgebraArchimedean => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedean_sound
  | .extendedMonotoneAlgebra => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebra_sound
  | .semanticLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabeling_sound
  | .predictiveLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabeling_sound
  | .rootLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabeling_sound
  | .selfLabelingEquational => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquational_sound
  | .finiteModelTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTermination_universal
  | .categoricalToposTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTermination_sound
  | .forwardClosures => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosures_universal
  | .matchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBounds_universal
  | .raiseConsistencyMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBounds_sound
  | .quasiDecreasingness => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingness_sound
  | .dpProcessorClassification => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassification_sound
  | .dpSubtermCriterion => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterion_sound
  | .dpArgumentFiltering => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFiltering_sound
  | .dpReductionPairProcessor => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessor_sound
  | .dpNeutralProcessors => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessors_sound
  | .dpReductionTriples => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriples_sound
  | .usableRulesMinimality => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimality_sound
  | .formativeRules => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRules_sound
  | .typeIntroduction => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroduction_universal
  | .manySortedPersistence => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistence_sound
  | .orderSortedDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDP_sound
  | .contextSensitiveDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDP_sound
  | .twoDDPForCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRS_sound
  | .operationalTerminationCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRS_sound
  | .integerTermRewriting => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewriting_sound
  | .lctrs => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrs_sound
  | .higherOrderLCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRS_sound
  | .horpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittance_sound
  | .cpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittance_sound
  | .generalSchemaAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittance_sound
  | .sizedTypesAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittance_sound
  | .coqGuardAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittance_sound
  | .bellantoniCookSplit => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplit_sound
  | .linearLogicTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrier_universal
  | .ramifiedRecursionTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrier_sound
  | .sharingNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativity_universal
  | .weightedTypeGraphEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscape_sound
  | .generalizedWeightedTypeGraphs => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphs_sound
  | .equationalQuotientNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativity_sound
  | .cycleRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicability_universal
  | .stringRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicability_universal
  | .leftLinearMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBounds_universal
  | .sizeChangeTerminationEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscape_sound
  | .infinitaryRewritingTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTermination_sound
  | .piCalculusTerminationTranslation => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslation_sound
  | .lambdaMuSNViaCPS => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPS_sound
  | .abstractInterpretationAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittance_sound
  | .quasiInterpretationsSharingAware => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAware_sound

/-- The defining-feature theorem of each row; the transfinite KBO feature is stated with
`Ordinal.{0}` and `NatOrdinal.{0}`. -/
def MethodFeature : RDRSMethodFamily → Prop
  | .standardKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOWitness_feature
  | .kboWithStatus => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusWitness_feature
  | .generalizedKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOWitness_feature
  | .subtermCoefficientKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOWitness_feature
  | .acKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOWitness_feature
  | .transfiniteKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOWitness_feature.{0, 0}
  | .lambdaFreeKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOWitness_feature
  | .acRPO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOWitness_feature
  | .rpoModuloPermutation => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationWitness_feature
  | .popStarFamily => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyWitness_feature
  | .simpleTerminationOrderType => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeWitness_feature
  | .cichonSlowGrowing => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingWitness_feature
  | .linearPolyQ => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQWitness_feature
  | .linearPolyR => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRWitness_feature
  | .negativeCoefficientPolynomial => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialWitness_feature
  | .maxPolynomial => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialWitness_feature
  | .nonlinearHigherDegreePolynomial => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialWitness_feature
  | .multilinearInterpretation => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationWitness_feature
  | .matrixNScalarProjection => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionWitness_feature
  | .matrixQRScalarProjection => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionWitness_feature
  | .arcticScalarProjection => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionWitness_feature
  | .tropicalScalarProjection => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionWitness_feature
  | .triangularMatrix => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixWitness_feature
  | .tupleInterpretationStrictS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSWitness_feature
  | .higherOrderTupleInterpretation => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness_feature
  | .polynomialKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOWitness_feature
  | .strictMonotoneAlgebraArchimedean => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanWitness_feature
  | .extendedMonotoneAlgebra => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraWitness_feature
  | .semanticLabeling => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingWitness_feature
  | .predictiveLabeling => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingWitness_feature
  | .rootLabeling => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingWitness_feature
  | .selfLabelingEquational => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalWitness_feature
  | .finiteModelTermination => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationWitness_feature
  | .categoricalToposTermination => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationWitness_feature
  | .forwardClosures => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresWitness_feature
  | .matchBounds => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsWitness_feature
  | .raiseConsistencyMatchBounds => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsWitness_feature
  | .quasiDecreasingness => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessWitness_feature
  | .dpProcessorClassification => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationWitness_feature
  | .dpSubtermCriterion => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionWitness_feature
  | .dpArgumentFiltering => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringWitness_feature
  | .dpReductionPairProcessor => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorWitness_feature
  | .dpNeutralProcessors => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsWitness_feature
  | .dpReductionTriples => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesWitness_feature
  | .usableRulesMinimality => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityWitness_feature
  | .formativeRules => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesWitness_feature
  | .typeIntroduction => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionWitness_feature
  | .manySortedPersistence => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceWitness_feature
  | .orderSortedDP => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPWitness_feature
  | .contextSensitiveDP => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPWitness_feature
  | .twoDDPForCTRS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSWitness_feature
  | .operationalTerminationCTRS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSWitness_feature
  | .integerTermRewriting => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingWitness_feature
  | .lctrs => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsWitness_feature
  | .higherOrderLCTRS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSWitness_feature
  | .horpoAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceWitness_feature
  | .cpoAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceWitness_feature
  | .generalSchemaAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceWitness_feature
  | .sizedTypesAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceWitness_feature
  | .coqGuardAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceWitness_feature
  | .bellantoniCookSplit => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitWitness_feature
  | .linearLogicTypingBarrier => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierWitness_feature
  | .ramifiedRecursionTypingBarrier => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierWitness_feature
  | .sharingNonConservativity => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityWitness_feature
  | .weightedTypeGraphEscape => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeWitness_feature
  | .generalizedWeightedTypeGraphs => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsWitness_feature
  | .equationalQuotientNonConservativity => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityWitness_feature
  | .cycleRewritingInapplicability => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityWitness_feature
  | .stringRewritingInapplicability => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityWitness_feature
  | .leftLinearMatchBounds => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsWitness_feature
  | .sizeChangeTerminationEscape => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeWitness_feature
  | .infinitaryRewritingTermination => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness_feature
  | .piCalculusTerminationTranslation => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationWitness_feature
  | .lambdaMuSNViaCPS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSWitness_feature
  | .abstractInterpretationAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceWitness_feature
  | .quasiInterpretationsSharingAware => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareWitness_feature

theorem methodFeature : ∀ f, MethodFeature f
  | .standardKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBOWitness_feature
  | .kboWithStatus => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatusWitness_feature
  | .generalizedKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBOWitness_feature
  | .subtermCoefficientKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBOWitness_feature
  | .acKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBOWitness_feature
  | .transfiniteKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBOWitness_feature.{0, 0}
  | .lambdaFreeKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBOWitness_feature
  | .acRPO => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPOWitness_feature
  | .rpoModuloPermutation => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutationWitness_feature
  | .popStarFamily => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamilyWitness_feature
  | .simpleTerminationOrderType => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderTypeWitness_feature
  | .cichonSlowGrowing => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowingWitness_feature
  | .linearPolyQ => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQWitness_feature
  | .linearPolyR => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyRWitness_feature
  | .negativeCoefficientPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomialWitness_feature
  | .maxPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomialWitness_feature
  | .nonlinearHigherDegreePolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomialWitness_feature
  | .multilinearInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretationWitness_feature
  | .matrixNScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjectionWitness_feature
  | .matrixQRScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjectionWitness_feature
  | .arcticScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjectionWitness_feature
  | .tropicalScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjectionWitness_feature
  | .triangularMatrix => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrixWitness_feature
  | .tupleInterpretationStrictS => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictSWitness_feature
  | .higherOrderTupleInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretationWitness_feature
  | .polynomialKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBOWitness_feature
  | .strictMonotoneAlgebraArchimedean => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedeanWitness_feature
  | .extendedMonotoneAlgebra => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebraWitness_feature
  | .semanticLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabelingWitness_feature
  | .predictiveLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabelingWitness_feature
  | .rootLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabelingWitness_feature
  | .selfLabelingEquational => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquationalWitness_feature
  | .finiteModelTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTerminationWitness_feature
  | .categoricalToposTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTerminationWitness_feature
  | .forwardClosures => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosuresWitness_feature
  | .matchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBoundsWitness_feature
  | .raiseConsistencyMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBoundsWitness_feature
  | .quasiDecreasingness => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingnessWitness_feature
  | .dpProcessorClassification => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassificationWitness_feature
  | .dpSubtermCriterion => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterionWitness_feature
  | .dpArgumentFiltering => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFilteringWitness_feature
  | .dpReductionPairProcessor => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessorWitness_feature
  | .dpNeutralProcessors => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessorsWitness_feature
  | .dpReductionTriples => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriplesWitness_feature
  | .usableRulesMinimality => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimalityWitness_feature
  | .formativeRules => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRulesWitness_feature
  | .typeIntroduction => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroductionWitness_feature
  | .manySortedPersistence => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistenceWitness_feature
  | .orderSortedDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDPWitness_feature
  | .contextSensitiveDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDPWitness_feature
  | .twoDDPForCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRSWitness_feature
  | .operationalTerminationCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRSWitness_feature
  | .integerTermRewriting => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewritingWitness_feature
  | .lctrs => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrsWitness_feature
  | .higherOrderLCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRSWitness_feature
  | .horpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittanceWitness_feature
  | .cpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittanceWitness_feature
  | .generalSchemaAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittanceWitness_feature
  | .sizedTypesAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittanceWitness_feature
  | .coqGuardAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittanceWitness_feature
  | .bellantoniCookSplit => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplitWitness_feature
  | .linearLogicTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrierWitness_feature
  | .ramifiedRecursionTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrierWitness_feature
  | .sharingNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativityWitness_feature
  | .weightedTypeGraphEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscapeWitness_feature
  | .generalizedWeightedTypeGraphs => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphsWitness_feature
  | .equationalQuotientNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativityWitness_feature
  | .cycleRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicabilityWitness_feature
  | .stringRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicabilityWitness_feature
  | .leftLinearMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBoundsWitness_feature
  | .sizeChangeTerminationEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscapeWitness_feature
  | .infinitaryRewritingTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTerminationWitness_feature
  | .piCalculusTerminationTranslation => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslationWitness_feature
  | .lambdaMuSNViaCPS => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPSWitness_feature
  | .abstractInterpretationAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittanceWitness_feature
  | .quasiInterpretationsSharingAware => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAwareWitness_feature

/-- The mutation control of each row. -/
def MethodMutation : RDRSMethodFamily → Prop
  | .standardKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBO_mutation
  | .kboWithStatus => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatus_mutation
  | .generalizedKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBO_mutation
  | .subtermCoefficientKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBO_mutation
  | .acKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBO_mutation
  | .transfiniteKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBO_mutation
  | .lambdaFreeKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBO_mutation
  | .acRPO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPO_mutation
  | .rpoModuloPermutation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutation_mutation
  | .popStarFamily => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamily_mutation
  | .simpleTerminationOrderType => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderType_mutation
  | .cichonSlowGrowing => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowing_mutation
  | .linearPolyQ => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQ_mutation
  | .linearPolyR => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyR_mutation
  | .negativeCoefficientPolynomial => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomial_mutation
  | .maxPolynomial => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomial_mutation
  | .nonlinearHigherDegreePolynomial => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomial_mutation
  | .multilinearInterpretation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretation_mutation
  | .matrixNScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjection_mutation
  | .matrixQRScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjection_mutation
  | .arcticScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjection_mutation
  | .tropicalScalarProjection => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjection_mutation
  | .triangularMatrix => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrix_mutation
  | .tupleInterpretationStrictS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictS_mutation
  | .higherOrderTupleInterpretation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretation_mutation
  | .polynomialKBO => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBO_mutation
  | .strictMonotoneAlgebraArchimedean => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedean_mutation
  | .extendedMonotoneAlgebra => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebra_mutation
  | .semanticLabeling => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabeling_mutation
  | .predictiveLabeling => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabeling_mutation
  | .rootLabeling => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabeling_mutation
  | .selfLabelingEquational => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquational_mutation
  | .finiteModelTermination => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTermination_mutation
  | .categoricalToposTermination => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTermination_mutation
  | .forwardClosures => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosures_mutation
  | .matchBounds => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBounds_mutation
  | .raiseConsistencyMatchBounds => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBounds_mutation
  | .quasiDecreasingness => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingness_mutation
  | .dpProcessorClassification => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassification_mutation
  | .dpSubtermCriterion => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterion_mutation
  | .dpArgumentFiltering => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFiltering_mutation
  | .dpReductionPairProcessor => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessor_mutation
  | .dpNeutralProcessors => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessors_mutation
  | .dpReductionTriples => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriples_mutation
  | .usableRulesMinimality => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimality_mutation
  | .formativeRules => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRules_mutation
  | .typeIntroduction => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroduction_mutation
  | .manySortedPersistence => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistence_mutation
  | .orderSortedDP => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDP_mutation
  | .contextSensitiveDP => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDP_mutation
  | .twoDDPForCTRS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRS_mutation
  | .operationalTerminationCTRS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRS_mutation
  | .integerTermRewriting => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewriting_mutation
  | .lctrs => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrs_mutation
  | .higherOrderLCTRS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRS_mutation
  | .horpoAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittance_mutation
  | .cpoAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittance_mutation
  | .generalSchemaAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittance_mutation
  | .sizedTypesAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittance_mutation
  | .coqGuardAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittance_mutation
  | .bellantoniCookSplit => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplit_mutation
  | .linearLogicTypingBarrier => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrier_mutation
  | .ramifiedRecursionTypingBarrier => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrier_mutation
  | .sharingNonConservativity => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativity_mutation
  | .weightedTypeGraphEscape => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscape_mutation
  | .generalizedWeightedTypeGraphs => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphs_mutation
  | .equationalQuotientNonConservativity => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativity_mutation
  | .cycleRewritingInapplicability => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicability_mutation
  | .stringRewritingInapplicability => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicability_mutation
  | .leftLinearMatchBounds => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBounds_mutation
  | .sizeChangeTerminationEscape => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscape_mutation
  | .infinitaryRewritingTermination => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTermination_mutation
  | .piCalculusTerminationTranslation => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslation_mutation
  | .lambdaMuSNViaCPS => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPS_mutation
  | .abstractInterpretationAdmittance => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittance_mutation
  | .quasiInterpretationsSharingAware => type_of% OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAware_mutation

theorem methodMutation : ∀ f, MethodMutation f
  | .standardKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.standardKBO_mutation
  | .kboWithStatus => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.kboWithStatus_mutation
  | .generalizedKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBO_mutation
  | .subtermCoefficientKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.subtermCoefficientKBO_mutation
  | .acKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBO_mutation
  | .transfiniteKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.transfiniteKBO_mutation
  | .lambdaFreeKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.lambdaFreeKBO_mutation
  | .acRPO => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.acRPO_mutation
  | .rpoModuloPermutation => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.rpoModuloPermutation_mutation
  | .popStarFamily => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.popStarFamily_mutation
  | .simpleTerminationOrderType => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderType_mutation
  | .cichonSlowGrowing => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.cichonSlowGrowing_mutation
  | .linearPolyQ => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyQ_mutation
  | .linearPolyR => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.linearPolyR_mutation
  | .negativeCoefficientPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.negativeCoefficientPolynomial_mutation
  | .maxPolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.maxPolynomial_mutation
  | .nonlinearHigherDegreePolynomial => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.nonlinearHigherDegreePolynomial_mutation
  | .multilinearInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.multilinearInterpretation_mutation
  | .matrixNScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixNScalarProjection_mutation
  | .matrixQRScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.matrixQRScalarProjection_mutation
  | .arcticScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.arcticScalarProjection_mutation
  | .tropicalScalarProjection => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tropicalScalarProjection_mutation
  | .triangularMatrix => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.triangularMatrix_mutation
  | .tupleInterpretationStrictS => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.tupleInterpretationStrictS_mutation
  | .higherOrderTupleInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretation_mutation
  | .polynomialKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.polynomialKBO_mutation
  | .strictMonotoneAlgebraArchimedean => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.strictMonotoneAlgebraArchimedean_mutation
  | .extendedMonotoneAlgebra => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.extendedMonotoneAlgebra_mutation
  | .semanticLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.semanticLabeling_mutation
  | .predictiveLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.predictiveLabeling_mutation
  | .rootLabeling => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.rootLabeling_mutation
  | .selfLabelingEquational => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.selfLabelingEquational_mutation
  | .finiteModelTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsInterpretations.finiteModelTermination_mutation
  | .categoricalToposTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTermination_mutation
  | .forwardClosures => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.forwardClosures_mutation
  | .matchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.matchBounds_mutation
  | .raiseConsistencyMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.raiseConsistencyMatchBounds_mutation
  | .quasiDecreasingness => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.quasiDecreasingness_mutation
  | .dpProcessorClassification => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpProcessorClassification_mutation
  | .dpSubtermCriterion => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpSubtermCriterion_mutation
  | .dpArgumentFiltering => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpArgumentFiltering_mutation
  | .dpReductionPairProcessor => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionPairProcessor_mutation
  | .dpNeutralProcessors => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpNeutralProcessors_mutation
  | .dpReductionTriples => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.dpReductionTriples_mutation
  | .usableRulesMinimality => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.usableRulesMinimality_mutation
  | .formativeRules => OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative.formativeRules_mutation
  | .typeIntroduction => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.typeIntroduction_mutation
  | .manySortedPersistence => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.manySortedPersistence_mutation
  | .orderSortedDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.orderSortedDP_mutation
  | .contextSensitiveDP => OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained.contextSensitiveDP_mutation
  | .twoDDPForCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.twoDDPForCTRS_mutation
  | .operationalTerminationCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.operationalTerminationCTRS_mutation
  | .integerTermRewriting => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.integerTermRewriting_mutation
  | .lctrs => OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained.lctrs_mutation
  | .higherOrderLCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRS_mutation
  | .horpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.horpoAdmittance_mutation
  | .cpoAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.cpoAdmittance_mutation
  | .generalSchemaAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.generalSchemaAdmittance_mutation
  | .sizedTypesAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi.sizedTypesAdmittance_mutation
  | .coqGuardAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.coqGuardAdmittance_mutation
  | .bellantoniCookSplit => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.bellantoniCookSplit_mutation
  | .linearLogicTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.linearLogicTypingBarrier_mutation
  | .ramifiedRecursionTypingBarrier => OperatorKO7.Methods.OrientationClosure.MethodRowsTypingDisciplines.ramifiedRecursionTypingBarrier_mutation
  | .sharingNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.sharingNonConservativity_mutation
  | .weightedTypeGraphEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscape_mutation
  | .generalizedWeightedTypeGraphs => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphs_mutation
  | .equationalQuotientNonConservativity => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.equationalQuotientNonConservativity_mutation
  | .cycleRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.cycleRewritingInapplicability_mutation
  | .stringRewritingInapplicability => OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate.stringRewritingInapplicability_mutation
  | .leftLinearMatchBounds => OperatorKO7.Methods.OrientationClosure.MethodRowsLabelingBounds.leftLinearMatchBounds_mutation
  | .sizeChangeTerminationEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs.sizeChangeTerminationEscape_mutation
  | .infinitaryRewritingTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTermination_mutation
  | .piCalculusTerminationTranslation => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslation_mutation
  | .lambdaMuSNViaCPS => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPS_mutation
  | .abstractInterpretationAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittance_mutation
  | .quasiInterpretationsSharingAware => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAware_mutation

/-- Rows whose exact named-method semantics were repaired in this closure. -/
inductive NamedMethodIdentityRow where
  | generalizedKBO
  | acKBO
  | simpleTerminationOrderType
  | higherOrderTupleInterpretation
  | infinitaryRewritingTermination
  | weightedTypeGraphEscape
  | generalizedWeightedTypeGraphs
  | quasiInterpretationsSharingAware
  | piCalculusTerminationTranslation
  | lambdaMuSNViaCPS
  | abstractInterpretationAdmittance
  | categoricalToposTermination
  | higherOrderLCTRS
  deriving DecidableEq, Repr

/-- Catalogue family represented by each repaired identity row. -/
def namedMethodFamily : NamedMethodIdentityRow → RDRSMethodFamily
  | .generalizedKBO => .generalizedKBO
  | .acKBO => .acKBO
  | .simpleTerminationOrderType => .simpleTerminationOrderType
  | .higherOrderTupleInterpretation => .higherOrderTupleInterpretation
  | .infinitaryRewritingTermination => .infinitaryRewritingTermination
  | .weightedTypeGraphEscape => .weightedTypeGraphEscape
  | .generalizedWeightedTypeGraphs => .generalizedWeightedTypeGraphs
  | .quasiInterpretationsSharingAware => .quasiInterpretationsSharingAware
  | .piCalculusTerminationTranslation => .piCalculusTerminationTranslation
  | .lambdaMuSNViaCPS => .lambdaMuSNViaCPS
  | .abstractInterpretationAdmittance => .abstractInterpretationAdmittance
  | .categoricalToposTermination => .categoricalToposTermination
  | .higherOrderLCTRS => .higherOrderLCTRS

/-- Exact source theorem type for each repaired named method. -/
def NamedMethodIdentity : NamedMethodIdentityRow → Prop
  | .generalizedKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBO_methodIdentity
  | .acKBO => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBO_methodIdentity
  | .simpleTerminationOrderType => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderType_methodIdentity
  | .higherOrderTupleInterpretation => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretation_methodIdentity
  | .infinitaryRewritingTermination => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTermination_methodIdentity
  | .weightedTypeGraphEscape => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscape_methodIdentity
  | .generalizedWeightedTypeGraphs => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphs_methodIdentity
  | .quasiInterpretationsSharingAware => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAware_methodIdentity
  | .piCalculusTerminationTranslation => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslation_methodIdentity
  | .lambdaMuSNViaCPS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPS_methodIdentity
  | .abstractInterpretationAdmittance => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittance_methodIdentity
  | .categoricalToposTermination => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTermination_methodIdentity
  | .higherOrderLCTRS => type_of% @OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRS_methodIdentity

/-- Every formerly unresolved row now carries its exact named-method theorem. -/
theorem namedMethodIdentity : ∀ r, NamedMethodIdentity r
  | .generalizedKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.generalizedKBO_methodIdentity
  | .acKBO => OperatorKO7.Methods.OrientationClosure.MethodRowsKBO.acKBO_methodIdentity
  | .simpleTerminationOrderType => OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders.simpleTerminationOrderType_methodIdentity
  | .higherOrderTupleInterpretation => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.higherOrderTupleInterpretation_methodIdentity
  | .infinitaryRewritingTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsOtherCalculi.infinitaryRewritingTermination_methodIdentity
  | .weightedTypeGraphEscape => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.weightedTypeGraphEscape_methodIdentity
  | .generalizedWeightedTypeGraphs => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.generalizedWeightedTypeGraphs_methodIdentity
  | .quasiInterpretationsSharingAware => OperatorKO7.Methods.OrientationClosure.MethodRowsGraphCalculi.quasiInterpretationsSharingAware_methodIdentity
  | .piCalculusTerminationTranslation => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.piCalculusTerminationTranslation_methodIdentity
  | .lambdaMuSNViaCPS => OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi.lambdaMuSNViaCPS_methodIdentity
  | .abstractInterpretationAdmittance => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.abstractInterpretationAdmittance_methodIdentity
  | .categoricalToposTermination => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.categoricalToposTermination_methodIdentity
  | .higherOrderLCTRS => OperatorKO7.Methods.OrientationClosure.MethodRowsSemanticFrameworks.higherOrderLCTRS_methodIdentity

/-- Catalogue families covered by the exact named-method repair. -/
def namedMethodIdentityRows : List RDRSMethodFamily :=
  [.generalizedKBO, .acKBO, .simpleTerminationOrderType, .higherOrderTupleInterpretation, .infinitaryRewritingTermination, .weightedTypeGraphEscape, .generalizedWeightedTypeGraphs, .quasiInterpretationsSharingAware, .piCalculusTerminationTranslation, .lambdaMuSNViaCPS, .abstractInterpretationAdmittance, .categoricalToposTermination, .higherOrderLCTRS]

theorem namedMethodIdentityRows_length : namedMethodIdentityRows.length = 13 := rfl

theorem namedMethodIdentityRows_nodup : namedMethodIdentityRows.Nodup := by decide

/-- The capstone: every method family has data satisfying its laws and its result. -/
theorem method_universe_closure :
    ∀ f : RDRSMethodFamily, ∃ M : MethodData f, MethodLaws f M ∧ MethodResult f M :=
  fun f => ⟨methodWitness f, methodWitness_laws f, methodWitness_result f⟩

/-- A certificate: a family, its data, and proofs of its laws and result. -/
structure RowCertificate where
  family : RDRSMethodFamily
  data : MethodData family
  laws : MethodLaws family data
  result : MethodResult family data

/-- The certificate of a family from its witness. -/
noncomputable def rowCertificate (f : RDRSMethodFamily) : RowCertificate :=
  ⟨f, methodWitness f, methodWitness_laws f, methodWitness_result f⟩

/-- The certificates, row by row. -/
noncomputable def certificates : List RowCertificate :=
  [rowCertificate .standardKBO,
    rowCertificate .kboWithStatus,
    rowCertificate .generalizedKBO,
    rowCertificate .subtermCoefficientKBO,
    rowCertificate .acKBO,
    rowCertificate .transfiniteKBO,
    rowCertificate .lambdaFreeKBO,
    rowCertificate .acRPO,
    rowCertificate .rpoModuloPermutation,
    rowCertificate .popStarFamily,
    rowCertificate .simpleTerminationOrderType,
    rowCertificate .cichonSlowGrowing,
    rowCertificate .linearPolyQ,
    rowCertificate .linearPolyR,
    rowCertificate .negativeCoefficientPolynomial,
    rowCertificate .maxPolynomial,
    rowCertificate .nonlinearHigherDegreePolynomial,
    rowCertificate .multilinearInterpretation,
    rowCertificate .matrixNScalarProjection,
    rowCertificate .matrixQRScalarProjection,
    rowCertificate .arcticScalarProjection,
    rowCertificate .tropicalScalarProjection,
    rowCertificate .triangularMatrix,
    rowCertificate .tupleInterpretationStrictS,
    rowCertificate .higherOrderTupleInterpretation,
    rowCertificate .polynomialKBO,
    rowCertificate .strictMonotoneAlgebraArchimedean,
    rowCertificate .extendedMonotoneAlgebra,
    rowCertificate .semanticLabeling,
    rowCertificate .predictiveLabeling,
    rowCertificate .rootLabeling,
    rowCertificate .selfLabelingEquational,
    rowCertificate .finiteModelTermination,
    rowCertificate .categoricalToposTermination,
    rowCertificate .forwardClosures,
    rowCertificate .matchBounds,
    rowCertificate .raiseConsistencyMatchBounds,
    rowCertificate .quasiDecreasingness,
    rowCertificate .dpProcessorClassification,
    rowCertificate .dpSubtermCriterion,
    rowCertificate .dpArgumentFiltering,
    rowCertificate .dpReductionPairProcessor,
    rowCertificate .dpNeutralProcessors,
    rowCertificate .dpReductionTriples,
    rowCertificate .usableRulesMinimality,
    rowCertificate .formativeRules,
    rowCertificate .typeIntroduction,
    rowCertificate .manySortedPersistence,
    rowCertificate .orderSortedDP,
    rowCertificate .contextSensitiveDP,
    rowCertificate .twoDDPForCTRS,
    rowCertificate .operationalTerminationCTRS,
    rowCertificate .integerTermRewriting,
    rowCertificate .lctrs,
    rowCertificate .higherOrderLCTRS,
    rowCertificate .horpoAdmittance,
    rowCertificate .cpoAdmittance,
    rowCertificate .generalSchemaAdmittance,
    rowCertificate .sizedTypesAdmittance,
    rowCertificate .coqGuardAdmittance,
    rowCertificate .bellantoniCookSplit,
    rowCertificate .linearLogicTypingBarrier,
    rowCertificate .ramifiedRecursionTypingBarrier,
    rowCertificate .sharingNonConservativity,
    rowCertificate .weightedTypeGraphEscape,
    rowCertificate .generalizedWeightedTypeGraphs,
    rowCertificate .equationalQuotientNonConservativity,
    rowCertificate .cycleRewritingInapplicability,
    rowCertificate .stringRewritingInapplicability,
    rowCertificate .leftLinearMatchBounds,
    rowCertificate .sizeChangeTerminationEscape,
    rowCertificate .infinitaryRewritingTermination,
    rowCertificate .piCalculusTerminationTranslation,
    rowCertificate .lambdaMuSNViaCPS,
    rowCertificate .abstractInterpretationAdmittance,
    rowCertificate .quasiInterpretationsSharingAware]

/-- The rows covered by the certificates. -/
noncomputable def coveredRows : List RDRSMethodFamily := certificates.map RowCertificate.family

/-- The covered rows are exactly the 76 families, in order. -/
theorem coveredRows_eq : coveredRows = allMethodFamilies := rfl

theorem coveredRows_length : coveredRows.length = 76 := by
  rw [coveredRows_eq]
  exact allMethodFamilies_length

/-- Control C26: removing any one certificate breaks the coverage equality. -/
theorem coverage_mutation (i : Nat) (hi : i < certificates.length) :
    (certificates.eraseIdx i).map RowCertificate.family ≠ allMethodFamilies := by
  intro h
  have hlen := congrArg List.length h
  rw [List.length_map, List.length_eraseIdx_of_lt hi, allMethodFamilies_length] at hlen
  have h76 : certificates.length = 76 := by
    have := coveredRows_length
    rwa [coveredRows, List.length_map] at this
  omega

end OperatorKO7.Methods.OrientationClosure.MethodUniverseClosure
