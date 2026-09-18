import OperatorKO7.Meta.RDRSCoverageEvidenceLedger

import OperatorKO7.Meta.RDRSDPProcessorClassification
import OperatorKO7.Meta.RDRSPathOrderDichotomy
import OperatorKO7.Meta.MatrixBarrierArbitrary
import OperatorKO7.Meta.MatrixBarrierArcticTropical
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.MaxBarrier
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.RDRSSemanticStructuralAtlas
import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas
import OperatorKO7.Meta.RDRSConditionalTypedAtlas
import OperatorKO7.Meta.RDRSNonConservativeEscapeAtlas
import OperatorKO7.Meta.Methods.UnarySignatureInapplicability
import OperatorKO7.Meta.Methods.PathOrderRows
import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows
import OperatorKO7.Meta.Methods.SemanticStructuralRows
import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import OperatorKO7.Meta.Methods.AdmittanceInapplicabilityRows
import OperatorKO7.Meta.Methods.SubstrateChangeRows
import OperatorKO7.Meta.Methods.ExactPromotionCarriers

#check @OperatorKO7.RDRSCoverageLedger.Evidence.rationalAffineInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.rationalAffineInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.realAffineInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.realAffineInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.naturalMatrixInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.naturalMatrixInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.triangularMatrixInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.triangularMatrixInterpretation
#check @OperatorKO7.Methods.NaturalMatrixInterpretationRows.naturalMatrix_exact_row
#print axioms OperatorKO7.Methods.NaturalMatrixInterpretationRows.naturalMatrix_exact_row
#check @OperatorKO7.Methods.NaturalMatrixInterpretationRows.triangularMatrix_exact_row
#print axioms OperatorKO7.Methods.NaturalMatrixInterpretationRows.triangularMatrix_exact_row

/-!
# Reach coverage for the RDRS coverage evidence ledger (WP-5)

Two jobs.

1. **NameGate.** Every distinct anchor String produced by
   `OperatorKO7.RDRSCoverageLedger.Full.leanTheoremIdentifierOf` is `#check @`-ed
   here against the live environment, with its full type printed. A String is
   never evidence; this file is what turns those Strings into checked names. If
   any anchor drifts, this file stops compiling.
2. **Reach.** Every public declaration added by
   `Meta/RDRSCoverageEvidenceLedger.lean` is reached, and the WP-5 gate
   conditions are restated as `example`s so they are checked, not narrated.
-/

namespace RDRSCoverageEvidenceLedgerReach

/-! ## 1. NameGate: every live ledger anchor, with its full type -/

/- KBO standard family. Repaired namespace: `KBOImpossible`, not
`KBO_Impossible`. -/
#check @OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace
#print axioms OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace

/- KBO variants. -/
#check @OperatorKO7.RDRSPathOrderDichotomy.kboBarrierVariant_no_symbolic_orientation
#print axioms OperatorKO7.RDRSPathOrderDichotomy.kboBarrierVariant_no_symbolic_orientation

/- Matrix arbitrary families. -/
#check @OperatorKO7.MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump
#print axioms OperatorKO7.MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump

/- Arctic and tropical scalar projections, split onto the two module-local
theorems that actually exist. -/
#check @OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_of_scalar_dominance_pump
#print axioms OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_of_scalar_dominance_pump
#check @OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_of_scalar_dominance_pump
#print axioms OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_tropicalMatrix_of_scalar_dominance_pump

/- Semantic and structural families. Repaired namespace: the atlas carries a
`Meta` component. -/
#check @OperatorKO7.Meta.RDRSSemanticStructuralAtlas.rdrs_semantic_structural_layer_closed
#print axioms OperatorKO7.Meta.RDRSSemanticStructuralAtlas.rdrs_semantic_structural_layer_closed

/- Algebraic interpretation families. -/
#check @OperatorKO7.PolynomialBarrierGeneral.no_global_step_orientation_polynomial_of_unbounded
#print axioms OperatorKO7.PolynomialBarrierGeneral.no_global_step_orientation_polynomial_of_unbounded
#check @OperatorKO7.MaxBarrier.no_global_step_orientation_max_of_unbounded
#print axioms OperatorKO7.MaxBarrier.no_global_step_orientation_max_of_unbounded
#check @OperatorKO7.MultilinearBarrier.no_global_step_orientation_multilinear_of_unbounded
#print axioms OperatorKO7.MultilinearBarrier.no_global_step_orientation_multilinear_of_unbounded
#check @OperatorKO7.RDRSAlgebraicInterpretationAtlas.rdrs_algebraic_interpretation_layer_closed
#print axioms OperatorKO7.RDRSAlgebraicInterpretationAtlas.rdrs_algebraic_interpretation_layer_closed

/- DP processor, path-order, conditional-typed, and nonconservative layers. -/
#check @OperatorKO7.RDRSDPProcessorClassification.rdrs_dp_processor_classification_closed
#print axioms OperatorKO7.RDRSDPProcessorClassification.rdrs_dp_processor_classification_closed
#check @OperatorKO7.RDRSPathOrderDichotomy.rdrs_path_order_layer_closed
#print axioms OperatorKO7.RDRSPathOrderDichotomy.rdrs_path_order_layer_closed
#check @OperatorKO7.RDRSConditionalTypedAtlas.rdrs_conditional_typed_layer_closed
#print axioms OperatorKO7.RDRSConditionalTypedAtlas.rdrs_conditional_typed_layer_closed
#check @OperatorKO7.RDRSNonConservativeEscapeAtlas.rdrs_nonconservative_escape_layer_closed
#print axioms OperatorKO7.RDRSNonConservativeEscapeAtlas.rdrs_nonconservative_escape_layer_closed

/-! ### Dispatch ORIENTATION exact native-row NameGate additions -/

#check @OperatorKO7.Methods.OrderedMatrixInterpretationRows.rational_real_matrix_exact_row
#print axioms OperatorKO7.Methods.OrderedMatrixInterpretationRows.rational_real_matrix_exact_row
#check @OperatorKO7.Methods.SemanticStructuralRows.finiteModelTermination_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.finiteModelTermination_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.matchBounds_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.matchBounds_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.raiseConsistencyMatchBounds_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.raiseConsistencyMatchBounds_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.quasiDecreasingness_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.quasiDecreasingness_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.categoricalToposTermination_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.categoricalToposTermination_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.forwardClosures_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.forwardClosures_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.popStarFamily_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.popStarFamily_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.simpleTerminationOrderType_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.simpleTerminationOrderType_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.dpReductionTriples_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.dpReductionTriples_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.formativeRules_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.formativeRules_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.typeIntroduction_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.typeIntroduction_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.manySortedPersistence_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.manySortedPersistence_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.orderSortedDP_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.orderSortedDP_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.contextSensitiveDP_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.contextSensitiveDP_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.operationalTerminationCTRS_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.operationalTerminationCTRS_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.integerTermRewriting_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.integerTermRewriting_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.lctrs_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.lctrs_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.higherOrderLCTRS_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.higherOrderLCTRS_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.horpoAdmittance_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.horpoAdmittance_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.cpoAdmittance_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.cpoAdmittance_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.bellantoniCookSplit_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.bellantoniCookSplit_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.ramifiedRecursionTypingBarrier_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.ramifiedRecursionTypingBarrier_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.sharingNonConservativity_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.sharingNonConservativity_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.weightedTypeGraphEscape_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.weightedTypeGraphEscape_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.generalizedWeightedTypeGraphs_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.generalizedWeightedTypeGraphs_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.leftLinearMatchBounds_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.leftLinearMatchBounds_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.infinitaryRewritingTermination_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.infinitaryRewritingTermination_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.piCalculusTerminationTranslation_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.piCalculusTerminationTranslation_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.lambdaMuSNViaCPS_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.lambdaMuSNViaCPS_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.quasiInterpretationsSharingAware_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.quasiInterpretationsSharingAware_row_anchor

/-! ## 2. NameGate: exact theorem-backed row anchors

The sixteen historical adapter-backed rows are checked first. Each row promoted
at the native-semantic layer is additionally checked through its method-row
certification theorem from `ExactPromotionCarriers`; none is admitted by a
generic proposition wrapper.  The exploratory local row anchors that remain
curated are NameGated afterward as research inputs, but are not evidence. -/

#check @OperatorKO7.RDRSCoverageLedger.Evidence.standardKBO_no_ko7_rec_succ
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.standardKBO_no_ko7_rec_succ
#check @OperatorKO7.KBOSubtermCoefficient.subtermCoefficientKBO_no_ko7_rec_succ
#print axioms OperatorKO7.KBOSubtermCoefficient.subtermCoefficientKBO_no_ko7_rec_succ
#check @OperatorKO7.Methods.ExactPromotionCarriers.cichonSlowGrowing_certifies
#print axioms OperatorKO7.Methods.ExactPromotionCarriers.cichonSlowGrowing_certifies
#check @OperatorKO7.RDRSCoverageLedger.Evidence.ko7_dpSubtermCriterion_row_anchor
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.ko7_dpSubtermCriterion_row_anchor
#check @OperatorKO7.Methods.ExactPromotionCarriers.argumentFiltering_certifies
#print axioms OperatorKO7.Methods.ExactPromotionCarriers.argumentFiltering_certifies
#check @OperatorKO7.Methods.ExactPromotionCarriers.neutralDPProcessor_certifies
#print axioms OperatorKO7.Methods.ExactPromotionCarriers.neutralDPProcessor_certifies
#check @OperatorKO7.RDRSCoverageLedger.Evidence.ko7_usableRules_rootClosure_minimality_anchor
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.ko7_usableRules_rootClosure_minimality_anchor
#check @OperatorKO7.Methods.ExactPromotionCarriers.sharing_certifies
#print axioms OperatorKO7.Methods.ExactPromotionCarriers.sharing_certifies
#check @OperatorKO7.Methods.ExactPromotionCarriers.equationalQuotient_certifies
#print axioms OperatorKO7.Methods.ExactPromotionCarriers.equationalQuotient_certifies
#check @OperatorKO7.Methods.UnarySignatureInapplicability.cycleRewriting_inapplicable
#print axioms OperatorKO7.Methods.UnarySignatureInapplicability.cycleRewriting_inapplicable
#check @OperatorKO7.Methods.UnarySignatureInapplicability.stringRewriting_inapplicable
#print axioms OperatorKO7.Methods.UnarySignatureInapplicability.stringRewriting_inapplicable
#check @OperatorKO7.Methods.ExactPromotionCarriers.sizeChange_certifies
#print axioms OperatorKO7.Methods.ExactPromotionCarriers.sizeChange_certifies

/- Exploratory local row anchors.  These resolve as declarations but remain
curated unless a separate exact carrier transport has been admitted above. -/
#check @OperatorKO7.Methods.PathOrderRows.kboWithStatus_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.kboWithStatus_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.generalizedKBO_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.generalizedKBO_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.acKBO_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.acKBO_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.transfiniteKBO_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.transfiniteKBO_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.lambdaFreeKBO_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.lambdaFreeKBO_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.polynomialKBO_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.polynomialKBO_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.acRPO_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.acRPO_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.rpoModuloPermutation_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.rpoModuloPermutation_row_anchor
#check @OperatorKO7.Methods.PathOrderRows.cichonSlowGrowing_row_anchor
#print axioms OperatorKO7.Methods.PathOrderRows.cichonSlowGrowing_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.linearPolyQ_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.linearPolyQ_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.linearPolyR_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.linearPolyR_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.negativeCoefficientPolynomial_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.negativeCoefficientPolynomial_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.maxPolynomial_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.maxPolynomial_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.nonlinearHigherDegreePolynomial_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.nonlinearHigherDegreePolynomial_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.multilinearInterpretation_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.multilinearInterpretation_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.matrixNScalarProjection_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.matrixNScalarProjection_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.matrixQRScalarProjection_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.matrixQRScalarProjection_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.arcticScalarProjection_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.arcticScalarProjection_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.tropicalScalarProjection_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.tropicalScalarProjection_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.triangularMatrix_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.triangularMatrix_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.tupleInterpretationStrictS_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.tupleInterpretationStrictS_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.higherOrderTupleInterpretation_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.higherOrderTupleInterpretation_row_anchor
#check @OperatorKO7.Methods.AlgebraicInterpretationRows.strictMonotoneAlgebraArchimedean_row_anchor
#print axioms OperatorKO7.Methods.AlgebraicInterpretationRows.strictMonotoneAlgebraArchimedean_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.extendedMonotoneAlgebra_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.extendedMonotoneAlgebra_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.semanticLabeling_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.semanticLabeling_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.predictiveLabeling_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.predictiveLabeling_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.rootLabeling_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.rootLabeling_row_anchor
#check @OperatorKO7.Methods.SemanticStructuralRows.selfLabelingEquational_row_anchor
#print axioms OperatorKO7.Methods.SemanticStructuralRows.selfLabelingEquational_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.dpProcessorClassification_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.dpProcessorClassification_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.dpArgumentFiltering_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.dpArgumentFiltering_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.dpReductionPairProcessor_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.dpReductionPairProcessor_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.dpNeutralProcessors_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.dpNeutralProcessors_row_anchor
#check @OperatorKO7.Methods.DependencyPairTypedRows.twoDDPForCTRS_row_anchor
#print axioms OperatorKO7.Methods.DependencyPairTypedRows.twoDDPForCTRS_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.generalSchemaAdmittance_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.generalSchemaAdmittance_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.sizedTypesAdmittance_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.sizedTypesAdmittance_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.coqGuardAdmittance_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.coqGuardAdmittance_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.linearLogicTypingBarrier_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.linearLogicTypingBarrier_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.abstractInterpretationAdmittance_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.abstractInterpretationAdmittance_row_anchor
#check @OperatorKO7.Methods.AdmittanceInapplicabilityRows.sizeChangeTerminationEscape_row_anchor
#print axioms OperatorKO7.Methods.AdmittanceInapplicabilityRows.sizeChangeTerminationEscape_row_anchor
#check @OperatorKO7.Methods.SubstrateChangeRows.equationalQuotientNonConservativity_row_anchor
#print axioms OperatorKO7.Methods.SubstrateChangeRows.equationalQuotientNonConservativity_row_anchor

/- Supporting anchors used by the carrier-side adapter laws. -/
#check @OperatorKO7.SymbolicComparatorBarrier.instantiate_dupSrc
#print axioms OperatorKO7.SymbolicComparatorBarrier.instantiate_dupSrc
#check @OperatorKO7.SymbolicComparatorBarrier.instantiate_dupTgt
#print axioms OperatorKO7.SymbolicComparatorBarrier.instantiate_dupTgt
#check @OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact
#print axioms OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact

/-! ## 3. Reach: every public declaration of the evidence ledger -/

section EvidenceReach

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSCoverageLedger.Full
open OperatorKO7.RDRSDPProcessorClassification
open OperatorKO7.RDRSCoverageLedger.Evidence
open OperatorKO7.Methods.ExactPromotionCarriers

#check @SchemaSymbol
#print axioms SchemaSymbol
#check @SchemaSymbol.base
#print axioms SchemaSymbol.base
#check @SchemaSymbol.succ
#print axioms SchemaSymbol.succ
#check @SchemaSymbol.wrap
#print axioms SchemaSymbol.wrap
#check @SchemaSymbol.recur
#print axioms SchemaSymbol.recur
#check @StandardKBO
#print axioms StandardKBO
#check @StandardKBO.mk
#print axioms StandardKBO.mk
#check @StandardKBO.variableWeight
#print axioms StandardKBO.variableWeight
#check @StandardKBO.variableWeight_pos
#print axioms StandardKBO.variableWeight_pos
#check @StandardKBO.symbolWeight
#print axioms StandardKBO.symbolWeight
#check @StandardKBO.constantWeight_ge_variable
#print axioms StandardKBO.constantWeight_ge_variable
#check @StandardKBO.precedenceRank
#print axioms StandardKBO.precedenceRank
#check @StandardKBO.precedenceRank_injective
#print axioms StandardKBO.precedenceRank_injective
#check @StandardKBO.zeroWeightOnlySucc
#print axioms StandardKBO.zeroWeightOnlySucc
#check @StandardKBO.zeroWeightSuccMaximal
#print axioms StandardKBO.zeroWeightSuccMaximal
#check @schemaKBOWeight
#print axioms schemaKBOWeight
#check @SchemaVariableCondition
#print axioms SchemaVariableCondition
#check @OperatorKO7.RDRSCoverageLedger.Evidence.STerm.matches
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.STerm.matches
#check @SuccIterationOfVar
#print axioms SuccIterationOfVar
#check @SuccIterationOfVar.once
#print axioms SuccIterationOfVar.once
#check @SuccIterationOfVar.more
#print axioms SuccIterationOfVar.more
#check @SchemaKBOGt
#print axioms SchemaKBOGt
#check @SchemaKBOGt.weight
#print axioms SchemaKBOGt.weight
#check @SchemaKBOGt.unaryVariable
#print axioms SchemaKBOGt.unaryVariable
#check @SchemaKBOGt.precedence
#print axioms SchemaKBOGt.precedence
#check @SchemaKBOGt.succLex
#print axioms SchemaKBOGt.succLex
#check @SchemaKBOGt.wrapLeftLex
#print axioms SchemaKBOGt.wrapLeftLex
#check @SchemaKBOGt.wrapRightLex
#print axioms SchemaKBOGt.wrapRightLex
#check @SchemaKBOGt.recurFirstLex
#print axioms SchemaKBOGt.recurFirstLex
#check @SchemaKBOGt.recurSecondLex
#print axioms SchemaKBOGt.recurSecondLex
#check @SchemaKBOGt.recurThirdLex
#print axioms SchemaKBOGt.recurThirdLex
#check @SchemaKBOGt.variableCondition
#print axioms SchemaKBOGt.variableCondition
#check @finiteStandardKBO
#print axioms finiteStandardKBO
#check @finiteStandardKBO_orients_strictWeight_witness
#print axioms finiteStandardKBO_orients_strictWeight_witness
#check @finiteStandardKBO_orients_precedence_witness
#print axioms finiteStandardKBO_orients_precedence_witness
#check @StandardKBORecSuccObstruction
#print axioms StandardKBORecSuccObstruction
#check @StandardKBORecSuccObstruction.mk
#print axioms StandardKBORecSuccObstruction.mk
#check @StandardKBORecSuccObstruction.noSchemaOrientation
#print axioms StandardKBORecSuccObstruction.noSchemaOrientation
#check @StandardKBORecSuccObstruction.sourceInstantiation
#print axioms StandardKBORecSuccObstruction.sourceInstantiation
#check @StandardKBORecSuccObstruction.targetInstantiation
#print axioms StandardKBORecSuccObstruction.targetInstantiation
#check @StandardKBORecSuccObstruction.actualRootStep
#print axioms StandardKBORecSuccObstruction.actualRootStep
#check @standardKBO_no_ko7_rec_succ
#print axioms standardKBO_no_ko7_rec_succ
#check @StandardKBORowClaim
#print axioms StandardKBORowClaim
#check @DPSubtermCriterionRowClaim
#print axioms DPSubtermCriterionRowClaim
#check @ko7_dpSubtermCriterion_row_anchor
#print axioms ko7_dpSubtermCriterion_row_anchor
#check @KO7RootRule
#print axioms KO7RootRule
#check @KO7RootRule.intDelta
#print axioms KO7RootRule.intDelta
#check @KO7RootRule.mergeVoidLeft
#print axioms KO7RootRule.mergeVoidLeft
#check @KO7RootRule.mergeVoidRight
#print axioms KO7RootRule.mergeVoidRight
#check @KO7RootRule.mergeCancel
#print axioms KO7RootRule.mergeCancel
#check @KO7RootRule.recZero
#print axioms KO7RootRule.recZero
#check @KO7RootRule.recSucc
#print axioms KO7RootRule.recSucc
#check @KO7RootRule.eqRefl
#print axioms KO7RootRule.eqRefl
#check @KO7RootRule.eqDiff
#print axioms KO7RootRule.eqDiff
#check @allKO7RootRules
#print axioms allKO7RootRules
#check @allKO7RootRules_nodup
#print axioms allKO7RootRules_nodup
#check @allKO7RootRules_complete
#print axioms allKO7RootRules_complete
#check @KO7DefinedRoot
#print axioms KO7DefinedRoot
#check @KO7DefinedRoot.integrate
#print axioms KO7DefinedRoot.integrate
#check @KO7DefinedRoot.merge
#print axioms KO7DefinedRoot.merge
#check @KO7DefinedRoot.recursor
#print axioms KO7DefinedRoot.recursor
#check @KO7DefinedRoot.equality
#print axioms KO7DefinedRoot.equality
#check @ko7RuleRoot
#print axioms ko7RuleRoot
#check @traceDefinedRoots
#print axioms traceDefinedRoots
#check @ko7RuleLhsTemplate
#print axioms ko7RuleLhsTemplate
#check @ko7RuleRhsTemplate
#print axioms ko7RuleRhsTemplate
#check @KO7RuleInstance
#print axioms KO7RuleInstance
#check @KO7RuleInstance.intDelta
#print axioms KO7RuleInstance.intDelta
#check @KO7RuleInstance.mergeVoidLeft
#print axioms KO7RuleInstance.mergeVoidLeft
#check @KO7RuleInstance.mergeVoidRight
#print axioms KO7RuleInstance.mergeVoidRight
#check @KO7RuleInstance.mergeCancel
#print axioms KO7RuleInstance.mergeCancel
#check @KO7RuleInstance.recZero
#print axioms KO7RuleInstance.recZero
#check @KO7RuleInstance.recSucc
#print axioms KO7RuleInstance.recSucc
#check @KO7RuleInstance.eqRefl
#print axioms KO7RuleInstance.eqRefl
#check @KO7RuleInstance.eqDiff
#print axioms KO7RuleInstance.eqDiff
#check @step_iff_complete_KO7RuleInstance
#print axioms step_iff_complete_KO7RuleInstance
#check @ko7RuleTemplate_is_ruleInstance
#print axioms ko7RuleTemplate_is_ruleInstance
#check @ko7RuleTemplate_is_actual_step
#print axioms ko7RuleTemplate_is_actual_step
#check @ko7RootDirectCallB
#print axioms ko7RootDirectCallB
#check @KO7RootDirectCall
#print axioms KO7RootDirectCall
#check @KO7RootClosed
#print axioms KO7RootClosed
#check @ko7CanonicalUsableRules
#print axioms ko7CanonicalUsableRules
#check @ko7CanonicalUsableRules_nodup
#print axioms ko7CanonicalUsableRules_nodup
#check @recSucc_directlyCalls_recZero
#print axioms recSucc_directlyCalls_recZero
#check @recSucc_directlyCalls_recSucc
#print axioms recSucc_directlyCalls_recSucc
#check @ko7CanonicalUsableRules_rootClosed
#print axioms ko7CanonicalUsableRules_rootClosed
#check @ko7CanonicalUsableRules_retains_recSucc
#print axioms ko7CanonicalUsableRules_retains_recSucc
#check @ko7CanonicalUsableRules_least
#print axioms ko7CanonicalUsableRules_least
#check @ko7CanonicalUsableRules_retained_recSucc_step
#print axioms ko7CanonicalUsableRules_retained_recSucc_step
#check @ko7DPRhsSchema
#print axioms ko7DPRhsSchema
#check @schemaDefinedRoots
#print axioms schemaDefinedRoots
#check @ko7DPRhsSchema_definedRoots
#print axioms ko7DPRhsSchema_definedRoots
#check @DPPair_rhs_schema_extraction
#print axioms DPPair_rhs_schema_extraction
#check @ko7RulesAtSchemaRoots
#print axioms ko7RulesAtSchemaRoots
#check @ko7RootClosureStep
#print axioms ko7RootClosureStep
#check @ko7GeneratedUsableRules
#print axioms ko7GeneratedUsableRules
#check @ko7RulesAtDPRhsRoots_exact
#print axioms ko7RulesAtDPRhsRoots_exact
#check @ko7GeneratedUsableRules_exact
#print axioms ko7GeneratedUsableRules_exact
#check @ko7GeneratedUsableRules_fixedPoint
#print axioms ko7GeneratedUsableRules_fixedPoint
#check @ko7GeneratedUsableRules_rootClosed
#print axioms ko7GeneratedUsableRules_rootClosed
#check @ko7GeneratedUsableRules_least
#print axioms ko7GeneratedUsableRules_least
#check @retainedDPProjection
#print axioms retainedDPProjection
#check @RetainedProjectionDecreases
#print axioms RetainedProjectionDecreases
#check @retainedProjection_decreases_on_DPPair
#print axioms retainedProjection_decreases_on_DPPair
#check @KO7DPPairUsableRulesCertificate
#print axioms KO7DPPairUsableRulesCertificate
#check @KO7DPPairUsableRulesCertificate.mk
#print axioms KO7DPPairUsableRulesCertificate.mk
#check @KO7DPPairUsableRulesCertificate.rhsSchemaExact
#print axioms KO7DPPairUsableRulesCertificate.rhsSchemaExact
#check @KO7DPPairUsableRulesCertificate.extractedRootsExact
#print axioms KO7DPPairUsableRulesCertificate.extractedRootsExact
#check @KO7DPPairUsableRulesCertificate.rulesGenerated
#print axioms KO7DPPairUsableRulesCertificate.rulesGenerated
#check @KO7DPPairUsableRulesCertificate.everyPairExtracts
#print axioms KO7DPPairUsableRulesCertificate.everyPairExtracts
#check @KO7DPPairUsableRulesCertificate.rulesExact
#print axioms KO7DPPairUsableRulesCertificate.rulesExact
#check @KO7DPPairUsableRulesCertificate.fixedPoint
#print axioms KO7DPPairUsableRulesCertificate.fixedPoint
#check @KO7DPPairUsableRulesCertificate.rootClosed
#print axioms KO7DPPairUsableRulesCertificate.rootClosed
#check @KO7DPPairUsableRulesCertificate.leastRootClosed
#print axioms KO7DPPairUsableRulesCertificate.leastRootClosed
#check @KO7DPPairUsableRulesCertificate.retainsDuplicatingRule
#print axioms KO7DPPairUsableRulesCertificate.retainsDuplicatingRule
#check @KO7DPPairUsableRulesCertificate.completeStepEnumeration
#print axioms KO7DPPairUsableRulesCertificate.completeStepEnumeration
#check @KO7DPPairUsableRulesCertificate.retainedProjectionStrict
#print axioms KO7DPPairUsableRulesCertificate.retainedProjectionStrict
#check @KO7DPPairUsableRulesCertificate.reversePairWellFounded
#print axioms KO7DPPairUsableRulesCertificate.reversePairWellFounded
#check @ko7_usableRules_rootClosure_minimality_anchor
#print axioms ko7_usableRules_rootClosure_minimality_anchor
#check @UsableRulesConcreteRowClaim
#print axioms UsableRulesConcreteRowClaim
#check @RowClaim
#print axioms RowClaim
#check @MethodInterpretation
#print axioms MethodInterpretation
#check @MethodInterpretation.kboVariableConditionOrder
#print axioms MethodInterpretation.kboVariableConditionOrder
#check @MethodInterpretation.subtermCoefficientKBOOrder
#print axioms MethodInterpretation.subtermCoefficientKBOOrder
#check @MethodInterpretation.cichonSlowGrowingMethod
#print axioms MethodInterpretation.cichonSlowGrowingMethod
#check @MethodInterpretation.dpSubtermProjectionRow
#print axioms MethodInterpretation.dpSubtermProjectionRow
#check @MethodInterpretation.dpArgumentFilteringMethod
#print axioms MethodInterpretation.dpArgumentFilteringMethod
#check @MethodInterpretation.dpNeutralProcessorMethod
#print axioms MethodInterpretation.dpNeutralProcessorMethod
#check @MethodInterpretation.usableRulesConcreteRow
#print axioms MethodInterpretation.usableRulesConcreteRow
#check @MethodInterpretation.sharingMethod
#print axioms MethodInterpretation.sharingMethod
#check @MethodInterpretation.equationalQuotientMethod
#print axioms MethodInterpretation.equationalQuotientMethod
#check @MethodInterpretation.cycleRewritingUnaryKill
#print axioms MethodInterpretation.cycleRewritingUnaryKill
#check @MethodInterpretation.stringRewritingUnaryKill
#print axioms MethodInterpretation.stringRewritingUnaryKill
#check @MethodInterpretation.sizeChangeMethod
#print axioms MethodInterpretation.sizeChangeMethod
#check @interpretedFamily
#print axioms interpretedFamily
#check @interpretedFamily_eq_index
#print axioms interpretedFamily_eq_index
#check @dpCarrier
#print axioms dpCarrier
#check @dpCarrier_eq_ko7DPSubtermCriterionExact
#print axioms dpCarrier_eq_ko7DPSubtermCriterionExact
#check @AnchorInstanceHolds
#print axioms AnchorInstanceHolds
#check @rowClaim_of_interpretation
#print axioms rowClaim_of_interpretation
#check @anchorInstance_of_rowClaim
#print axioms anchorInstance_of_rowClaim
#check @anchorInstance_holds
#print axioms anchorInstance_holds
#check @TheoremBackedEvidence
#print axioms TheoremBackedEvidence
#check @TheoremBackedEvidence.interpretation
#print axioms TheoremBackedEvidence.interpretation
#check @TheoremBackedEvidence.anchorInstance
#print axioms TheoremBackedEvidence.anchorInstance
#check @TheoremBackedEvidence.rowClaim
#print axioms TheoremBackedEvidence.rowClaim
#check @theoremBackedEvidenceOf
#print axioms theoremBackedEvidenceOf
#check @standardKBOInterpretation
#print axioms standardKBOInterpretation
#check @subtermCoefficientKBOInterpretation
#print axioms subtermCoefficientKBOInterpretation
#check @cichonSlowGrowingInterpretation
#print axioms cichonSlowGrowingInterpretation
#check @dpArgumentFilteringInterpretation
#print axioms dpArgumentFilteringInterpretation
#check @dpNeutralProcessorInterpretation
#print axioms dpNeutralProcessorInterpretation
#check @usableRulesInterpretation
#print axioms usableRulesInterpretation
#check @sharingInterpretation
#print axioms sharingInterpretation
#check @equationalQuotientInterpretation
#print axioms equationalQuotientInterpretation
#check @cycleRewritingInterpretation
#print axioms cycleRewritingInterpretation
#check @stringRewritingInterpretation
#print axioms stringRewritingInterpretation
#check @sizeChangeInterpretation
#print axioms sizeChangeInterpretation
#check @CuratedReason
#print axioms CuratedReason
#check @CuratedReason.noTransportAdapter
#print axioms CuratedReason.noTransportAdapter
#check @CuratedReason.externalNonLane
#print axioms CuratedReason.externalNonLane
#check @CuratedReason.substrateChange
#print axioms CuratedReason.substrateChange
#check @CuratedReason.importDependent
#print axioms CuratedReason.importDependent
#check @curatedReason?
#print axioms curatedReason?
#check @curated_row_has_no_semantic_claim
#print axioms curated_row_has_no_semantic_claim
#check @curated_methodInterpretation_isEmpty
#print axioms curated_methodInterpretation_isEmpty
#check @CuratedDisposition
#print axioms CuratedDisposition
#check @CuratedDisposition.mk
#print axioms CuratedDisposition.mk
#check @CuratedDisposition.reasonAssigned
#print axioms CuratedDisposition.reasonAssigned
#check @CuratedDisposition.noSemanticClaim
#print axioms CuratedDisposition.noSemanticClaim
#check @CuratedDisposition.noInterpretation
#print axioms CuratedDisposition.noInterpretation
#check @CuratedDisposition.definiteClass
#print axioms CuratedDisposition.definiteClass
#check @curatedDisposition_of_reason
#print axioms curatedDisposition_of_reason
#check @RowDisposition
#print axioms RowDisposition
#check @RowDisposition.theoremBacked
#print axioms RowDisposition.theoremBacked
#check @RowDisposition.curated
#print axioms RowDisposition.curated
#check @RowDisposition.isTheoremBacked
#print axioms RowDisposition.isTheoremBacked
#check @rowDisposition
#print axioms rowDisposition
#check @InterpretationResolution
#print axioms InterpretationResolution
#check @interpretationResolution
#print axioms interpretationResolution
#check @interpretationResolution_total
#print axioms interpretationResolution_total
#check @theoremBackedRows
#print axioms theoremBackedRows
#check @curatedRows
#print axioms curatedRows
#check @theoremBackedRows_mem_iff
#print axioms theoremBackedRows_mem_iff
#check @curatedRows_mem_iff
#print axioms curatedRows_mem_iff
#check @curated_rows_have_no_interpretation
#print axioms curated_rows_have_no_interpretation
#check @theoremBackedRows_nodup
#print axioms theoremBackedRows_nodup
#check @curatedRows_nodup
#print axioms curatedRows_nodup
#check @buckets_disjoint
#print axioms buckets_disjoint
#check @buckets_complete
#print axioms buckets_complete
#check @theoremBackedRows_count
#print axioms theoremBackedRows_count
#check @curatedRows_count
#print axioms curatedRows_count
#check @split_total
#print axioms split_total
#check @theoremBackedRows_nonempty
#print axioms theoremBackedRows_nonempty
#check @theoremBackedRows_eq
#print axioms theoremBackedRows_eq
#check @curatedRowsWithReason
#print axioms curatedRowsWithReason
#check @curated_noTransportAdapter_count
#print axioms curated_noTransportAdapter_count
#check @curated_externalNonLane_count
#print axioms curated_externalNonLane_count
#check @curated_substrateChange_count
#print axioms curated_substrateChange_count
#check @curated_importDependent_count
#print axioms curated_importDependent_count
#check @curated_reason_partition
#print axioms curated_reason_partition
#check @rowDisposition_matches_split
#print axioms rowDisposition_matches_split
#check @theoremBackedRows_eq_disposition_filter
#print axioms theoremBackedRows_eq_disposition_filter
#check @curatedRows_eq_disposition_filter
#print axioms curatedRows_eq_disposition_filter
#check @buckets_append_perm_allMethodFamilies
#print axioms buckets_append_perm_allMethodFamilies
#check @buckets_append_mem_iff
#print axioms buckets_append_mem_iff
#check @theoremBacked_rows_have_interpretations
#print axioms theoremBacked_rows_have_interpretations
#check @theoremBacked_rows_have_evidence
#print axioms theoremBacked_rows_have_evidence
#check @theoremBacked_rows_inhabit_rowClaim
#print axioms theoremBacked_rows_inhabit_rowClaim
#check @CoverageEvidenceLedgerClosed
#print axioms CoverageEvidenceLedgerClosed
#check @CoverageEvidenceLedgerClosed.mk
#print axioms CoverageEvidenceLedgerClosed.mk
#check @CoverageEvidenceLedgerClosed.dispositionTotal
#print axioms CoverageEvidenceLedgerClosed.dispositionTotal
#check @CoverageEvidenceLedgerClosed.theoremBackedFilterExact
#print axioms CoverageEvidenceLedgerClosed.theoremBackedFilterExact
#check @CoverageEvidenceLedgerClosed.curatedFilterExact
#print axioms CoverageEvidenceLedgerClosed.curatedFilterExact
#check @CoverageEvidenceLedgerClosed.disjoint
#print axioms CoverageEvidenceLedgerClosed.disjoint
#check @CoverageEvidenceLedgerClosed.complete
#print axioms CoverageEvidenceLedgerClosed.complete
#check @CoverageEvidenceLedgerClosed.bucketPermutation
#print axioms CoverageEvidenceLedgerClosed.bucketPermutation
#check @CoverageEvidenceLedgerClosed.theoremBackedCount
#print axioms CoverageEvidenceLedgerClosed.theoremBackedCount
#check @CoverageEvidenceLedgerClosed.curatedCount
#print axioms CoverageEvidenceLedgerClosed.curatedCount
#check @CoverageEvidenceLedgerClosed.totalRows
#print axioms CoverageEvidenceLedgerClosed.totalRows
#check @CoverageEvidenceLedgerClosed.theoremBackedNonempty
#print axioms CoverageEvidenceLedgerClosed.theoremBackedNonempty
#check @CoverageEvidenceLedgerClosed.everyTheoremBackedRowHasAdapter
#print axioms CoverageEvidenceLedgerClosed.everyTheoremBackedRowHasAdapter
#check @CoverageEvidenceLedgerClosed.everyTheoremBackedRowInhabitsClaim
#print axioms CoverageEvidenceLedgerClosed.everyTheoremBackedRowInhabitsClaim
#check @CoverageEvidenceLedgerClosed.everyCuratedRowHasNoInterpretation
#print axioms CoverageEvidenceLedgerClosed.everyCuratedRowHasNoInterpretation
#check @CoverageEvidenceLedgerClosed.everyRowHasResolution
#print axioms CoverageEvidenceLedgerClosed.everyRowHasResolution
#check @CoverageEvidenceLedgerClosed.noCuratedRowClaimsSemantics
#print axioms CoverageEvidenceLedgerClosed.noCuratedRowClaimsSemantics
#check @CoverageEvidenceLedgerClosed.zeroUnclassified
#print axioms CoverageEvidenceLedgerClosed.zeroUnclassified
#check @rdrs_coverage_evidence_ledger_closed
#print axioms rdrs_coverage_evidence_ledger_closed
#check @OperatorKO7.RDRSCoverageLedger.Evidence.rdrs_coverage_evidence_ledger_anchor
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.rdrs_coverage_evidence_ledger_anchor

/-! ### Dispatch ORIENTATION 76-row indexed interpretation layer -/

#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation.legacy
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation.legacy
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation.orientation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation.orientation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.curated_row_has_missingNativeInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.curated_row_has_missingNativeInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeMethodInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeMethodInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.every_row_has_native_interpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.every_row_has_native_interpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeRowClaim
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeRowClaim
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.legacyNativeRows_eq_theoremBackedRows
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.legacyNativeRows_eq_theoremBackedRows
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeRowClaim_closed
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeRowClaim_closed
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodEvidence
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodEvidence
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeMethodEvidence
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeMethodEvidence
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows_count
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeTheoremBackedRows_count
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows_count
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.nativeCuratedRows_count
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.native_split_total
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.native_split_total
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.every_native_row_has_evidence
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.every_native_row_has_evidence
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.native_rows_exactly_allMethodFamilies
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.native_rows_exactly_allMethodFamilies
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.mk
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.mk
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.totalRows
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.totalRows
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.zeroNativeCurated
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.zeroNativeCurated
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.exactUniverse
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.exactUniverse
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.everyRowHasNativeInterpretation
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.everyRowHasNativeInterpretation
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.everyRowHasNativeEvidence
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.everyRowHasNativeEvidence
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.legacyAdapterSplitPreserved
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.legacyAdapterSplitPreserved
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.complementaryWaveExact
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.complementaryWaveExact
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.researchPackages
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed.researchPackages
#check @OperatorKO7.RDRSCoverageLedger.Evidence.Native.rdrs_native_coverage_evidence_ledger_closed
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.Native.rdrs_native_coverage_evidence_ledger_closed
#check @OperatorKO7.RDRSCoverageLedger.Evidence.rdrs_native_coverage_evidence_ledger_anchor
#print axioms OperatorKO7.RDRSCoverageLedger.Evidence.rdrs_native_coverage_evidence_ledger_anchor

/-! ## 4. Gate examples -/

/- Gate: the historical adapter capstone holds. -/
example : CoverageEvidenceLedgerClosed := rdrs_coverage_evidence_ledger_closed

/- Gate: the ORIENTATION closeout is not proposition-only. Every row carries an
indexed native interpretation object and the 60-row complement has exactly the
same identities as the interpretation-bearing ORIENTATION list. -/
example (f : RDRSMethodFamily) :
    Nonempty (OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeMethodInterpretation f) :=
  OperatorKO7.RDRSCoverageLedger.Evidence.Native.every_row_has_native_interpretation f

example :
    OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeInterpretationRows.length = 60 :=
  OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeInterpretationRows_count

example :
    OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeInterpretationRows =
      OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeRows :=
  OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage.missingNativeInterpretationRows_eq_missingNativeRows

example : OperatorKO7.RDRSCoverageLedger.Evidence.Native.NativeCoverageEvidenceLedgerClosed :=
  OperatorKO7.RDRSCoverageLedger.Evidence.Native.rdrs_native_coverage_evidence_ledger_closed

/- Gate: exactly 76 rows, split exactly. -/
example : theoremBackedRows.length + curatedRows.length = 76 := split_total

/- Gate: the exact theorem-backed count after proof-bearing promotion. -/
example : theoremBackedRows.length = 16 := theoremBackedRows_count

/- Gate: the complementary curated count. -/
example : curatedRows.length = 60 := curatedRows_count

/- Gate: the theorem-backed subset is non-empty. Zero would be a failed
semantic repair. -/
example : theoremBackedRows.length > 0 := theoremBackedRows_nonempty

/- Gate: the exact sixteen-row membership theorem itself is reached above as
`theoremBackedRows_eq`; its right-hand side is the ordered explicit row list. -/

/- Gate: the `subtermCoefficientKBO` row claim reduces to the carrier-specialized
theorem over every admissible KBO with subterm coefficients, not to a relation
that merely satisfies an unweighted variable condition. -/
example :
    ∀ K : OperatorKO7.KBOSubtermCoefficient.SubtermCoefficientKBO,
      OperatorKO7.KBOSubtermCoefficient.SubtermCoefficientKBORecSuccObstruction K :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.subtermCoefficientKBO (by decide)

/- Gate: zero unclassified rows in the underlying status ledger. -/
example : temporaryUnclassifiedFamilies.length = 0 := temporary_unclassified_count

/- Gate: the `standardKBO` row claim reduces to the carrier-specialized theorem
over the actual finite standard-KBO definition, not an arbitrary relation that
merely happens to satisfy a variable-condition premise. -/
example : ∀ K : StandardKBO, StandardKBORecSuccObstruction K :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.standardKBO (by decide)

/- Gate: the `dpSubtermCriterion` row claim exposes the canonical certificate,
both index conventions, strict descent on the actual DP relation, and
well-foundedness of its reverse. -/
example :
    OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact.projectionIndex = 2
      ∧ OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact.projectionIndex_paper = 3
      ∧ (∀ {a b : OperatorKO7.Trace},
          OperatorKO7.MetaDependencyPairs.DPPair a b →
            OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact.rank b
              < OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact.rank a)
      ∧ WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.dpSubtermCriterion (by decide)

/- Gate: the `usableRulesMinimality` row exposes the actual least finite KO7
root closure generated from the symbolic DP RHS, retains the duplicating rule,
and carries the exact DP projection certificate. It makes no generic
source-termination claim. -/
example : KO7DPPairUsableRulesCertificate ko7DPRhsSchema
    (ko7GeneratedUsableRules ko7DPRhsSchema) :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.usableRulesMinimality (by decide)

/- Gate: every newly promoted row inhabits its exact closed-carrier row claim. -/
example : CichonSlowGrowingExactRowClaim :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.cichonSlowGrowing (by decide)

example : ArgumentFilteringExactRowClaim :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.dpArgumentFiltering (by decide)

example : NeutralDPProcessorExactRowClaim :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.dpNeutralProcessors (by decide)

example : SharingExactRowClaim :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.sharingNonConservativity (by decide)

example : EquationalQuotientExactRowClaim :=
  theoremBacked_rows_inhabit_rowClaim
    RDRSMethodFamily.equationalQuotientNonConservativity (by decide)

example : SizeChangeExactRowClaim :=
  theoremBacked_rows_inhabit_rowClaim RDRSMethodFamily.sizeChangeTerminationEscape (by decide)

/- Gate: specialization is on the exact same method object carried by each
interpretation; there is no row-level proof laundering step. -/
example : CichonSlowGrowingCertifies .guardedContextual :=
  anchorInstance_holds cichonSlowGrowingInterpretation

example : ArgumentFilteringCertifies .counterOnly :=
  anchorInstance_holds dpArgumentFilteringInterpretation

example : NeutralDPProcessorCertifies .identity :=
  anchorInstance_holds dpNeutralProcessorInterpretation

example : SharingCertifies .explicitSharedNode :=
  anchorInstance_holds sharingInterpretation

example : EquationalQuotientCertifies .mergeCommutativity :=
  anchorInstance_holds equationalQuotientInterpretation

example : SizeChangeCertifies .schemaSingleCall :=
  anchorInstance_holds sizeChangeInterpretation

/- Gate: the DP subterm row's claim really carries well-foundedness of the
reversed DP pair relation at its own carrier, so the row is not backed by a
tautology. -/
example : WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev :=
  (anchorInstance_holds MethodInterpretation.dpSubtermProjectionRow).2.2.2

/- Gate: the usable-rules carrier proves leastness for every closed candidate. -/
example (rules : List KO7RootRule) (hclosed : KO7RootClosed rules)
    (hseed : KO7RootRule.recSucc ∈ rules) :
    ∀ q, q ∈ ko7GeneratedUsableRules ko7DPRhsSchema → q ∈ rules :=
  (anchorInstance_holds usableRulesInterpretation).1.leastRootClosed rules hclosed hseed

/- Gate: the carrier consumes its actual retained-pair witness to obtain strict
projection descent on that same pair. -/
example : RetainedProjectionDecreases
    (ko7GeneratedUsableRules ko7DPRhsSchema)
    (OperatorKO7.MetaDependencyPairs.DPPair.rec_succ
      OperatorKO7.Trace.void OperatorKO7.Trace.void OperatorKO7.Trace.void) :=
  (anchorInstance_holds usableRulesInterpretation).2

/- Gate: the finite rule enumeration is extensionally exact for the live
kernel `Step`, not merely a self-declared complete enum. -/
example {x y : OperatorKO7.Trace} :
    OperatorKO7.Step x y ↔
      ∃ r, r ∈ allKO7RootRules ∧ KO7RuleInstance r x y :=
  step_iff_complete_KO7RuleInstance

/- Gate: a genuinely curated row inhabits no semantic claim. Status assignment
alone gives nothing. -/
example : ¬ RowClaim RDRSMethodFamily.popStarFamily (u6ClassOf RDRSMethodFamily.popStarFamily) :=
  curated_row_has_no_semantic_claim RDRSMethodFamily.popStarFamily (by decide)

/- Gate: the interpretation's family projection is computed, not stored. -/
example : interpretedFamily standardKBOInterpretation = RDRSMethodFamily.standardKBO :=
  interpretedFamily_eq_index standardKBOInterpretation

/- Gate: the DP interpretation computes the exact canonical certificate. -/
example : dpCarrier MethodInterpretation.dpSubtermProjectionRow =
    some OperatorKO7.DPSubtermCriterionExactNS.ko7DPSubtermCriterionExact := rfl

/- Gate: the quantified standard-KBO carrier is inhabited and its strict-weight
and precedence arms both orient concrete, distinct schema terms. -/
example : SchemaKBOGt finiteStandardKBO (.succ .base) .base :=
  finiteStandardKBO_orients_strictWeight_witness

example : SchemaKBOGt finiteStandardKBO (.wrap .base .base) (.succ (.succ .base)) :=
  finiteStandardKBO_orients_precedence_witness

/- Gate: the repaired KBO anchor String is the one the evidence layer uses. -/
example :
    leanTheoremIdentifierOf RDRSMethodFamily.standardKBO
      = "OperatorKO7.RDRSCoverageLedger.Evidence.standardKBO_no_ko7_rec_succ" := rfl

/- Gate: the DP and usable-rules strings point to their typed semantic anchors,
not the finite DP status classifier. -/
example :
    leanTheoremIdentifierOf RDRSMethodFamily.dpSubtermCriterion
      = "OperatorKO7.RDRSCoverageLedger.Evidence.ko7_dpSubtermCriterion_row_anchor" := rfl

example :
    leanTheoremIdentifierOf RDRSMethodFamily.usableRulesMinimality
      = "OperatorKO7.RDRSCoverageLedger.Evidence.ko7_usableRules_rootClosure_minimality_anchor" := rfl

/- Gate: matrix row identifiers point to the corresponding method theorem. -/
example :
    leanTheoremIdentifierOf RDRSMethodFamily.matrixNScalarProjection =
      "OperatorKO7.Methods.NaturalMatrixInterpretationRows.naturalMatrix_exact_row" := rfl

example :
    leanTheoremIdentifierOf RDRSMethodFamily.triangularMatrix =
      "OperatorKO7.Methods.NaturalMatrixInterpretationRows.triangularMatrix_exact_row" := rfl

/- Gate: the match-bounds identifier names the native row anchor. -/
example :
    leanTheoremIdentifierOf RDRSMethodFamily.matchBounds
      = "OperatorKO7.Methods.SemanticStructuralRows.matchBounds_row_anchor" :=
  rfl

end EvidenceReach

end RDRSCoverageEvidenceLedgerReach
